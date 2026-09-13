from __future__ import annotations

import fcntl
import json
import os
import re
import shutil
import signal
import subprocess
import tempfile
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from difflib import SequenceMatcher
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Iterable
from unicodedata import normalize as unicode_normalize

from .blind_eval import command as blind_eval_command
from .blind_eval import enabled as blind_eval_enabled
from .config import TaskConfig
from .frontends.policies import get_policy
from .lean import (
    extract_lean_declarations,
    find_environment_declaration,
    glob_files,
    inspect_lean_environment,
    mask_lean_comments_and_strings,
    module_name_for_path,
)
from .util import (
    PipelineError,
    normalize_space,
    read_json,
    sha256_bytes,
    sha256_file,
    sha256_json,
    write_json,
)


JUDGE_VERSION = 10
PROMPT_VERSION = "semantic-alignment-v27"
SUPPORTED_PROMPT_VERSIONS = (
    "semantic-alignment-v1",
    "semantic-alignment-v2",
    "semantic-alignment-v3",
    "semantic-alignment-v4",
    "semantic-alignment-v5",
    "semantic-alignment-v6",
    "semantic-alignment-v7",
    "semantic-alignment-v8",
    "semantic-alignment-v9",
    "semantic-alignment-v10",
    "semantic-alignment-v11",
    "semantic-alignment-v12",
    "semantic-alignment-v13",
    "semantic-alignment-v14",
    "semantic-alignment-v15",
    "semantic-alignment-v16",
    "semantic-alignment-v17",
    "semantic-alignment-v18",
    "semantic-alignment-v19",
    "semantic-alignment-v20",
    "semantic-alignment-v21",
    "semantic-alignment-v22",
    "semantic-alignment-v23",
    "semantic-alignment-v24",
    "semantic-alignment-v25",
    "semantic-alignment-v26",
    "semantic-alignment-v27",
)


def aligned_example_requirement(prompt_version: str = PROMPT_VERSION) -> int:
    """Return the minimum bilateral examples required for aligned verdicts."""
    return 3


TARGET_INDEX = "target-index.json"
JUDGE_PLAN = "judge-plan.json"
JUDGE_REPORT_JSON = "judge-report.json"
JUDGE_REPORT_MD = "judge-report.md"
JUDGE_DIRECTORY = "judge"
JUDGE_SCHEMA = "verdict-schema.json"

THEOREM_KINDS = {
    "Theorem",
    "Lemma",
    "Corollary",
    "Proposition",
    "Remark",
    "Fact",
    "corollary",
    "lemma",
    "lemmas",
    "proposition",
    "schematic_goal",
    "theorem",
}
DEFINITION_KINDS = {
    "Definition",
    "Fixpoint",
    "CoFixpoint",
    "Program Definition",
    "Program Fixpoint",
    "Equations",
    "Canonical Structure",
    "Instance",
    "Program Instance",
    "abbreviation",
    "definition",
    "fun",
    "function",
    "lift_definition",
    "primrec",
}
TYPE_KINDS = {
    "Inductive",
    "CoInductive",
    "Variant",
    "Structure",
    "Record",
    "Class",
    "class",
    "coinductive",
    "datatype",
    "inductive",
    "inductive_set",
    "locale",
    "nominal_datatype",
    "quotient_type",
    "type_synonym",
    "typedef",
}
FAILURE_CATEGORIES = {
    "added_precondition",
    "removed_precondition",
    "weakened_postcondition",
    "strengthened_postcondition",
    "domain_mismatch",
    "codomain_mismatch",
    "dependent_result_erased",
    "definition_behavior_mismatch",
    "inductive_constructor_mismatch",
    "representation_bridge_missing",
    "quantifier_or_binder_mismatch",
    "wrong_constant_or_relation",
    "vacuous_or_trivialized_statement",
    "missing_source_item",
    "missing_target_item",
    "wrong_item_match",
    "dependency_or_context_mismatch",
    "source_domain_loss",
    "target_domain_extension",
    "interface_relation_failure",
    "visibility_mismatch",
    "other",
}

LEAN_IMPORT_RE = re.compile(
    r"(?m)^[ \t]*(?:public[ \t]+)?import[ \t]+(?P<name>[A-Za-z0-9_'.]+)"
)
IDENTIFIER_RE = re.compile(r"(?<![A-Za-z0-9_'])[A-Za-z_][A-Za-z0-9_'.]*")


VERDICT_SCHEMA: dict[str, Any] = {
    "$schema": "https://json-schema.org/draft/2020-12/schema",
    "type": "object",
    "additionalProperties": False,
    "required": [
        "source_id",
        "target_id",
        "match_status",
        "alignment",
        "confidence",
        "source_summary",
        "target_summary",
        "failure_categories",
        "differences",
        "interface_witness",
        "examples",
        "counterexamples",
        "suggested_target",
        "target_disposition",
        "evidence",
        "compiler_surface_checks",
    ],
    "properties": {
        "source_id": {"type": ["string", "null"]},
        "target_id": {"type": ["string", "null"]},
        "match_status": {
            "type": "string",
            "enum": [
                "confirmed",
                "wrong_match",
                "source_unmatched",
                "target_unmatched",
                "uncertain",
            ],
        },
        "alignment": {
            "type": "string",
            "enum": ["aligned", "not_aligned", "uncertain", "not_judged"],
        },
        "confidence": {"type": "number", "minimum": 0, "maximum": 1},
        "source_summary": {"type": "string"},
        "target_summary": {"type": "string"},
        "failure_categories": {
            "type": "array",
            "items": {"type": "string", "enum": sorted(FAILURE_CATEGORIES)},
        },
        "differences": {"type": "array", "items": {"type": "string"}},
        "interface_witness": {
            "type": "object",
            "additionalProperties": False,
            "required": [
                "status",
                "kind",
                "source_interface",
                "target_interface",
                "explanation",
                "compiler_validated",
            ],
            "properties": {
                "status": {
                    "type": "string",
                    "enum": ["found", "not_found", "not_applicable"],
                },
                "kind": {
                    "type": ["string", "null"],
                    "enum": [
                        "domain_mismatch",
                        "codomain_mismatch",
                        "arity_mismatch",
                        "binder_mismatch",
                        "source_domain_loss",
                        "target_domain_extension",
                        "interface_relation_failure",
                        "visibility_mismatch",
                        None,
                    ],
                },
                "source_interface": {"type": ["string", "null"]},
                "target_interface": {"type": ["string", "null"]},
                "explanation": {"type": "string"},
                "compiler_validated": {"type": "boolean"},
            },
        },
        "examples": {
            "type": "array",
            "items": {"$ref": "#/$defs/observation_pair"},
        },
        "counterexamples": {
            "type": "array",
            "items": {"$ref": "#/$defs/observation_pair"},
        },
        "suggested_target": {
            "type": ["object", "null"],
            "additionalProperties": False,
            "required": ["id", "reason"],
            "properties": {
                "id": {"type": "string"},
                "reason": {"type": "string"},
            },
        },
        "target_disposition": {
            "type": ["string", "null"],
            "enum": [
                "helper_or_bridge",
                "proof_of_matched_spec",
                "duplicate_translation",
                "unrelated_addition",
                "uncertain",
                None,
            ],
        },
        "evidence": {
            "type": "array",
            "items": {
                "type": "object",
                "additionalProperties": False,
                "required": ["side", "file", "line", "description"],
                "properties": {
                    "side": {"type": "string", "enum": ["source", "target"]},
                    "file": {"type": "string"},
                    "line": {"type": "integer", "minimum": 1},
                    "description": {"type": "string"},
                },
            },
        },
        "compiler_surface_checks": {
            "type": "array",
            "items": {
                "type": "object",
                "additionalProperties": False,
                "required": ["source_name", "disposition", "target_evidence"],
                "properties": {
                    "source_name": {"type": "string"},
                    "disposition": {
                        "type": "string",
                        "enum": [
                            "preserved_explicitly",
                            "preserved_by_target_native_api",
                            "nonsemantic_generated_internal",
                            "missing_or_misaligned",
                            "uncertain",
                        ],
                    },
                    "target_evidence": {"type": "string"},
                },
            },
        },
    },
    "$defs": {
        "run": {
            "type": "object",
            "additionalProperties": False,
            "required": [
                "language",
                "mode",
                "entrypoint",
                "invocation",
                "claim",
                "code",
                "expected_stdout",
            ],
            "properties": {
                "language": {
                    "type": "string",
                    "enum": ["coq", "isabelle", "lean"],
                },
                "mode": {
                    "type": "string",
                    "enum": ["prove", "evaluate"],
                },
                "entrypoint": {"type": ["string", "null"]},
                "invocation": {"type": "string", "minLength": 1},
                "claim": {"type": "string", "minLength": 1},
                "code": {"type": "string"},
                "expected_stdout": {"type": ["string", "null"]},
            },
        },
        "observation_side": {
            "type": "object",
            "additionalProperties": False,
            "required": ["subject", "input", "output", "run"],
            "properties": {
                "subject": {"type": "string", "minLength": 1},
                "input": {
                    "type": "object",
                    "additionalProperties": False,
                    "required": ["description", "expression"],
                    "properties": {
                        "description": {"type": "string", "minLength": 1},
                        "expression": {"type": "string", "minLength": 1},
                    },
                },
                "output": {
                    "type": "object",
                    "additionalProperties": False,
                    "required": ["description", "expression"],
                    "properties": {
                        "description": {"type": "string", "minLength": 1},
                        "expression": {"type": "string", "minLength": 1},
                    },
                },
                "run": {"$ref": "#/$defs/run"},
            },
        },
        "alignment_claim": {
            "type": "object",
            "additionalProperties": False,
            "required": ["status", "reason"],
            "properties": {
                "status": {
                    "type": "string",
                    "enum": ["same", "different", "uncertain"],
                },
                "reason": {"type": "string", "minLength": 1},
            },
        },
        "observation_pair": {
            "type": "object",
            "additionalProperties": False,
            "required": [
                "id",
                "source",
                "target",
                "input_alignment",
                "output_alignment",
            ],
            "properties": {
                "id": {"type": "string", "minLength": 1},
                "source": {"$ref": "#/$defs/observation_side"},
                "target": {"$ref": "#/$defs/observation_side"},
                "input_alignment": {"$ref": "#/$defs/alignment_claim"},
                "output_alignment": {"$ref": "#/$defs/alignment_claim"},
            },
        },
    },
}


def _lean_role(path: str) -> str:
    parts = set(Path(path).parts)
    if "Spec" in parts:
        return "specification"
    if "Proof" in parts:
        return "proof"
    if "Impl" in parts:
        return "implementation"
    if parts & {"ModuleTests", "Tests", "Test"} or Path(path).name.lower().startswith(
        "test"
    ):
        return "test"
    return "public"


def _target_signature(text: str) -> str:
    positions = [
        position
        for marker in (":=", "\nwhere", "\n  where")
        if (position := text.find(marker)) >= 0
    ]
    return text[: min(positions)].strip() if positions else text.strip()


def _dependency_ids(
    items: list[dict[str, Any]],
    *,
    text_field: str,
    name_field: str = "name",
) -> dict[str, list[str]]:
    by_basename: dict[str, list[str]] = defaultdict(list)
    for item in items:
        # Match-only structure fields model Coq Module Type Parameters. Do not
        # let their generated projection names rewrite the dependency payload
        # of every existing declaration with the same token.
        if item.get("match_only"):
            continue
        by_basename[item[name_field].split(".")[-1]].append(item["id"])
    result: dict[str, list[str]] = {}
    for item in items:
        tokens = {
            token.rstrip(".").split(".")[-1]
            for token in IDENTIFIER_RE.findall(item.get(text_field, ""))
        }
        dependencies = {
            dependency
            for token in tokens
            for dependency in by_basename.get(token, [])
            if dependency != item["id"]
        }
        result[item["id"]] = sorted(dependencies)
    return result


def build_target_index(task: TaskConfig) -> dict[str, Any]:
    """Extract source ranges and validate every compilable Lean module.

    A repository-wide build is diagnostic only.  A broken downstream module must
    not prevent lexical indexing or environment confirmation of independent,
    compilable modules; hierarchical judging applies the actual compile gate to
    each semantic module scope.
    """
    project = task.target.project
    if not project.is_dir():
        raise PipelineError(f"target project does not exist: {project}")
    compile_preflight: dict[str, Any] | None = None
    if any(
        (project / filename).is_file()
        for filename in ("lakefile.toml", "lakefile.lean")
    ):
        compile_preflight = _run_command(
            ["lake", "build", *task.target.build_targets],
            cwd=project,
            timeout=task.acceptance.build_timeout_seconds,
        )
    paths = glob_files(project, task.target.lean_globs)
    declarations: list[dict[str, Any]] = []
    files: list[dict[str, Any]] = []
    source_annotations_by_declaration: dict[str, set[str]] = defaultdict(set)
    for path in paths:
        relative = path.relative_to(project).as_posix()
        raw = path.read_text(encoding="utf-8")
        clean = mask_lean_comments_and_strings(raw)
        extracted = extract_lean_declarations(
            raw, include_structure_fields=True
        )
        for match in re.finditer(
            r"(?m)^[ \t]*--[ \t]*Source ID:[ \t]*(?P<source>\S+)[ \t]*$"
            r"\n^[ \t]*--[ \t]*Target:[ \t]*(?P<target>\S+)[ \t]*$",
            raw,
        ):
            item = next(
                (item for item in extracted if item["start"] >= match.end()),
                None,
            )
            if item is None or match.group("target") not in {
                item["name"], item.get("qualified_name", item["name"])
            }:
                continue
            identifier = f"{relative}:{item['name']}:{item['line']}"
            source_annotations_by_declaration[identifier].add(
                match.group("source")
            )
        imports = [
            match.group("name") for match in LEAN_IMPORT_RE.finditer(clean)
        ]
        ids: list[str] = []
        parent_ids = {
            (item["name"], item["line"]): f"{relative}:{item['name']}:{item['line']}"
            for item in extracted
            if item["kind"] != "field"
        }
        parent_lines = {
            item["name"]: item["line"]
            for item in extracted
            if item["kind"] != "field"
        }
        for item in extracted:
            if item["kind"] == "field":
                line_end = raw.find("\n", item["start"])
                text = raw[
                    item["start"] : len(raw) if line_end < 0 else line_end
                ].strip()
            else:
                text = raw[item["start"] : item["end"]].strip()
            line = item["line"]
            name = item["name"]
            identifier = f"{relative}:{name}:{line}"
            ids.append(identifier)
            declaration = {
                "id": identifier,
                "name": name,
                "qualified_name": item.get("qualified_name", name),
                "kind": item["kind"],
                "modifiers": item["modifiers"],
                "target_file": relative,
                "target_line": line,
                "role": _lean_role(relative),
                "judge_eligible": _lean_role(relative) != "test",
                "match_eligible": _lean_role(relative) != "test",
                "unmatched_eligible": _lean_role(relative) != "test",
                "target_signature": _target_signature(text),
                "target_text": text,
                "dependencies": [],
            }
            if item["kind"] == "field":
                parent_name = item["parent_name"]
                declaration.update(
                    {
                        "parent_id": parent_ids[
                            (parent_name, parent_lines[parent_name])
                        ],
                        # Coq extraction records Module Type Parameters as
                        # source items, while ordinary Record fields are folded
                        # into their parent. Fields are candidates only for
                        # source Parameters and do not create unmatched jobs.
                        "match_only": True,
                        "judge_eligible": False,
                        "match_eligible": True,
                        "unmatched_eligible": False,
                    }
                )
            declarations.append(declaration)
        files.append(
            {
                "target_file": relative,
                "target_sha256": sha256_file(path),
                "imports": imports,
                "declaration_ids": ids,
            }
        )

    environment_modules = [
        module_name_for_path(item["target_file"])
        for item in files
        if _lean_role(item["target_file"]) != "test"
    ]
    environment = inspect_lean_environment(
        project,
        environment_modules,
        timeout_seconds=300,
    )
    if environment["status"] == "failed":
        whole_environment = environment
        per_module: list[dict[str, Any]] = []
        with ThreadPoolExecutor(max_workers=min(8, len(environment_modules) or 1)) as executor:
            futures = {
                executor.submit(
                    inspect_lean_environment,
                    project,
                    [module],
                    timeout_seconds=300,
                ): module
                for module in environment_modules
            }
            for future in as_completed(futures):
                module = futures[future]
                try:
                    result = future.result()
                except Exception as exc:
                    result = {
                        "status": "failed",
                        "modules": [module],
                        "declarations": [],
                        "diagnostic": f"module environment inspection failed: {exc}",
                    }
                per_module.append(result)
        passed = [item for item in per_module if item.get("status") == "passed"]
        declarations_from_modules = [
            declaration
            for item in passed
            for declaration in item.get("declarations", [])
        ]
        environment = {
            "status": "partial" if passed else "failed",
            "mode": "lean_environment_per_module_fallback",
            "modules": sorted(environment_modules),
            "declarations": sorted(
                declarations_from_modules,
                key=lambda item: (item["module"], item["name"]),
            ),
            "returncode": None,
            "stdout": "",
            "stderr": whole_environment.get("stderr", ""),
            "diagnostic": whole_environment.get("diagnostic", ""),
            "whole_repository_probe": {
                key: value
                for key, value in whole_environment.items()
                if key not in {"stdout", "declarations"}
            },
            "module_probes": [
                {
                    key: value
                    for key, value in item.items()
                    if key not in {"stdout", "declarations"}
                }
                for item in sorted(
                    per_module,
                    key=lambda item: (item.get("modules") or [""])[0],
                )
            ],
            "confirmed_modules": sorted(
                module
                for item in passed
                for module in item.get("modules", [])
            ),
            "failed_modules": sorted(
                module
                for item in per_module
                if item.get("status") != "passed"
                for module in item.get("modules", [])
            ),
        }
    confirmed_environment_names: set[str] = set()
    explicit_environment_owners: dict[str, dict[str, Any]] = {}
    for declaration in declarations:
        module = module_name_for_path(declaration["target_file"])
        elaborated = find_environment_declaration(
            environment,
            module,
            declaration["qualified_name"],
        )
        if elaborated is not None:
            confirmed_environment_names.add(elaborated["name"])
            explicit_environment_owners[elaborated["name"]] = declaration
            elaborated["association"] = "explicit_source_declaration"
            elaborated["target_id"] = declaration["id"]
            declaration.update(
                {
                    "qualified_name": elaborated["name"],
                    "environment_confirmed": True,
                    "environment_kind": elaborated["kind"],
                    "elaborated_type": elaborated["type"],
                    "environment_unsafe": elaborated["unsafe"],
                    "environment_partial": elaborated["partial"],
                }
            )
        else:
            declaration["environment_confirmed"] = False
        annotated_source_ids = (
            sorted(source_annotations_by_declaration.get(declaration["id"], set()))
            if declaration["environment_confirmed"]
            else []
        )
        if annotated_source_ids:
            declaration["annotated_source_ids"] = annotated_source_ids

    generated_association_count = 0
    for item in environment.get("declarations", []):
        if item["name"] in confirmed_environment_names:
            continue
        owners = [
            (qualified_name, declaration)
            for qualified_name, declaration in explicit_environment_owners.items()
            if module_name_for_path(declaration["target_file"]) == item["module"]
            and (
                item["name"].startswith(f"{qualified_name}.")
                or item["name"] == f"{qualified_name}_def"
            )
        ]
        if not owners:
            continue
        owner_name, owner = max(owners, key=lambda candidate: len(candidate[0]))
        item.update(
            {
                "association": "generated_from_explicit_declaration",
                "generated_from_target_id": owner["id"],
                "generated_from_qualified_name": owner_name,
            }
        )
        generated_association_count += 1

    dependency_map = _dependency_ids(declarations, text_field="target_text")
    target_by_id = {item["id"]: item for item in declarations}
    for declaration in declarations:
        dependencies = dependency_map[declaration["id"]]
        if declaration.get("parent_id"):
            dependencies = sorted(
                {*dependencies, declaration["parent_id"]}
            )
        declaration["dependencies"] = dependencies
        if declaration["role"] == "proof" and any(
            target_by_id[dependency]["role"] == "specification"
            for dependency in dependencies
            if dependency in target_by_id
        ):
            declaration["unmatched_eligible"] = False
            declaration["inventory_disposition"] = "proof_of_specification"
    environment_summary = {
        key: value
        for key, value in environment.items()
        if key not in {"stdout"}
    }
    environment_summary["unassociated_declarations"] = [
        item
        for item in environment.get("declarations", [])
        if "association" not in item
    ]
    environment_summary["associated_declaration_count"] = len(
        confirmed_environment_names
    )
    environment_summary["unassociated_declaration_count"] = len(
        environment_summary["unassociated_declarations"]
    )
    environment_summary["generated_association_count"] = (
        generated_association_count
    )
    typed = environment["status"] in {"passed", "partial"}
    return {
        "version": JUDGE_VERSION,
        "task_id": task.task_id,
        "target": {
            "language": "lean4",
            "project": str(project),
            "import_module": task.target.import_module,
        },
        "extraction": {
            "mode": (
                "shared_lexical_plus_lean_environment"
                if typed
                else "shared_lexical_environment_unavailable"
            ),
            "typed": typed,
            "limitations": [
                "Source ranges and approximate dependencies are extracted lexically.",
                "Lean's compiled environment is authoritative for elaborated "
                "names, kinds, and types when available.",
                "Generated declarations are recorded in the environment inventory "
                "but do not independently create unmatched-target jobs.",
                "Structure fields are indexed as match-only projection candidates "
                "and checked against the environment.",
                "The repository-wide build is diagnostic; semantic module scopes "
                "receive independent compile gates during hierarchical judging.",
            ],
        },
        "environment": environment_summary,
        "compile_preflight": compile_preflight,
        "file_count": len(files),
        "declaration_count": len(declarations),
        "files": files,
        "declarations": declarations,
    }


def build_source_dependency_graph(source_index: dict[str, Any]) -> dict[str, Any]:
    declarations = source_index.get("declarations", [])
    if all("dependency_ids" in item for item in declarations):
        return dependency_graph(
            [item["id"] for item in declarations],
            {
                item["id"]: item.get("dependency_ids", [])
                for item in declarations
            },
        )
    judge_items = [
        {
            **item,
            "_judge_text": "\n".join(
                [
                    *item.get("section_context", []),
                    item.get("source_signature", ""),
                    item.get("proof") or "",
                    *item.get("program_obligations", []),
                ]
            ),
        }
        for item in declarations
    ]
    dependency_map = _dependency_ids(judge_items, text_field="_judge_text")
    return dependency_graph(
        [item["id"] for item in judge_items], dependency_map
    )


def dependency_graph(
    nodes: Iterable[str], dependencies: dict[str, list[str]]
) -> dict[str, Any]:
    """Return deterministic topological layers and any cyclic residual."""
    ordered_nodes = sorted(set(nodes))
    node_set = set(ordered_nodes)
    remaining = {
        node: set(dependencies.get(node, [])) & node_set
        for node in ordered_nodes
    }
    layers: list[list[str]] = []
    emitted: set[str] = set()
    while True:
        layer = sorted(
            node
            for node, edges in remaining.items()
            if node not in emitted and not (edges - emitted)
        )
        if not layer:
            break
        layers.append(layer)
        emitted.update(layer)
    cyclic = sorted(node_set - emitted)
    return {
        "nodes": ordered_nodes,
        "edges": {
            node: sorted(remaining[node])
            for node in ordered_nodes
            if remaining[node]
        },
        "topological_layers": layers,
        "cyclic_or_unresolved": cyclic,
    }


@lru_cache(maxsize=None)
def _normalized_name(name: str) -> str:
    base = name.split(".")[-1]
    base = re.sub(r"\\<\^sub>([A-Za-z0-9])", r"\1", base)
    base = unicode_normalize("NFKD", base)
    for prefix in ("spec_", "source_", "translated_"):
        if base.startswith(prefix):
            base = base[len(prefix) :]
    for suffix in ("_spec", "_source_bridge"):
        if base.endswith(suffix):
            base = base[: -len(suffix)]
    return re.sub(r"[^a-z0-9]", "", base.lower())


def _source_role(kind: str) -> str:
    if kind in THEOREM_KINDS:
        return "theorem"
    if kind in DEFINITION_KINDS:
        return "definition"
    if kind in TYPE_KINDS:
        return "type"
    return "other"


def _kind_score(source: dict[str, Any], target: dict[str, Any]) -> float:
    role = _source_role(source["kind"])
    target_kind = target["kind"]
    target_role = target["role"]
    if role == "theorem":
        if target_role == "specification":
            return 0.30
        if target_role == "proof" and target_kind in {"theorem", "lemma"}:
            return 0.18
        if target_kind in {"theorem", "lemma"}:
            return 0.14
        return 0.02
    if role == "definition":
        return 0.30 if target_role == "implementation" else 0.04
    if role == "type":
        if target_kind in {"inductive", "structure", "class"}:
            return 0.28
        return 0.03
    return 0.05


def _source_context_names(source: dict[str, Any]) -> list[str]:
    names: list[str] = []
    for context in source.get("context", []):
        if not isinstance(context, dict):
            continue
        name = context.get("name")
        if not isinstance(name, str) or not name:
            continue
        names.append(name.split(".")[-1])
    return names


_INTERFACE_SYMBOL_STOPWORDS = {
    "abs", "app", "bool", "bound", "const", "false", "free", "fun",
    "list", "nat", "none", "prop", "pure", "set", "some", "true",
    "type", "universe",
}


def _interface_symbol_tokens(value: Any) -> frozenset[str]:
    """Return conservative cross-prover interface landmarks."""
    if not isinstance(value, str):
        return frozenset()
    return _cached_interface_symbol_tokens(value)


@lru_cache(maxsize=None)
def _cached_interface_symbol_tokens(value: str) -> frozenset[str]:
    tokens: set[str] = set()
    for raw in re.findall(r"[A-Za-z][A-Za-z0-9_']*", value):
        normalized = re.sub(r"[^a-z0-9]", "", raw.lower())
        if (
            len(normalized) >= 3
            and normalized not in _INTERFACE_SYMBOL_STOPWORDS
            and (raw[0].isupper() or "_" in raw)
        ):
            tokens.add(normalized)
    return frozenset(tokens)


@lru_cache(maxsize=None)
def _surface_identifier_basenames(value: str) -> frozenset[str]:
    return frozenset(
        token.rstrip(".").split(".")[-1]
        for token in IDENTIFIER_RE.findall(value)
    )


@lru_cache(maxsize=None)
def _context_identifier_pattern(name: str) -> re.Pattern[str]:
    return re.compile(
        rf"(?<![A-Za-z0-9_']){re.escape(name)}(?![A-Za-z0-9_'])"
    )


def _match_score(source: dict[str, Any], target: dict[str, Any]) -> tuple[float, list[str]]:
    if source.get("id") in target.get("annotated_source_ids", []):
        return 2.0, ["compiler-checked Source ID/Target annotation"]
    if (
        source.get("kind", "").lower() == "coercion"
        and target.get("kind") != "instance"
    ):
        return 0.0, []
    source_base = source["name"].split(".")[-1]
    target_base = target["name"].split(".")[-1]
    source_normalized = _normalized_name(source_base)
    target_normalized = _normalized_name(target_base)
    reasons: list[str] = []
    if source_base == target_base:
        score = 0.62
        reasons.append("exact basename")
    elif source_normalized == target_normalized and source_normalized:
        score = 0.56
        reasons.append("normalized basename")
    else:
        # SequenceMatcher's ratio is 2*M/(len(a)+len(b)), with M bounded by
        # the shorter name.  Avoid its quadratic work when 0.78 is impossible.
        ratio_upper = (
            2 * min(len(source_normalized), len(target_normalized))
            / (len(source_normalized) + len(target_normalized))
            if source_normalized or target_normalized
            else 0.0
        )
        ratio = (
            SequenceMatcher(None, source_normalized, target_normalized).ratio()
            if ratio_upper >= 0.78
            else 0.0
        )
        score = 0.42 * ratio if ratio >= 0.78 else 0.0
        if score:
            reasons.append(f"name similarity {ratio:.3f}")
    kind_score = _kind_score(source, target)
    score += kind_score
    if kind_score:
        reasons.append(f"role/kind compatibility {kind_score:.2f}")
    source_stem = _normalized_name(Path(source["source_file"]).stem)
    target_stem = _normalized_name(Path(target["target_file"]).stem)
    if source_stem == target_stem:
        score += 0.08
        reasons.append("source/target module stem")
    target_namespace = {
        _normalized_name(part)
        for part in target.get("qualified_name", target["name"]).split(".")[:-1]
    }
    if (
        source_normalized
        and source_normalized == target_normalized
        and source_stem in target_namespace
    ):
        score += 0.20
        reasons.append("source module/target namespace")
    target_identity_surface = "\n".join(
        str(target.get(field, ""))
        for field in ("qualified_name", "target_signature", "elaborated_type")
    )
    target_full_surface = target_identity_surface + "\n" + str(
        target.get("target_text", "")
    )
    target_identity_names = _surface_identifier_basenames(target_identity_surface)
    source_qualified = str(
        source.get("fully_qualified_name") or source.get("qualified_name") or ""
    ).split(".")
    target_qualified = str(
        target.get("qualified_name") or target.get("name") or ""
    ).split(".")
    if (
        len(source_qualified) > 1
        and len(target_qualified) > 1
        and source_normalized == target_normalized
        and _normalized_name(source_qualified[-2])
        == _normalized_name(target_qualified[-2])
    ):
        score += 0.24
        reasons.append("compiler-qualified immediate namespace")
    for context_name in _source_context_names(source):
        if context_name in target_identity_names:
            score += 0.16
            reasons.append(f"source context {context_name}")
            break
        if _context_identifier_pattern(context_name).search(target_full_surface):
            score += 0.04
            reasons.append(f"referenced source context {context_name}")
            break
    # Prefer the compiler-selected public type. A named Isabelle theorem
    # bundle's lexical command mentions every member, while its selected
    # compiler entity identifies the member represented by this normalized
    # item (for example pfresh_simps(1) / PVr rather than PAp or PLm).
    source_interface = source.get("type_signature") or source.get(
        "source_signature", ""
    )
    source_symbols = _interface_symbol_tokens(source_interface)
    target_symbols = _interface_symbol_tokens(
        "\n".join(
            str(target.get(field, ""))
            for field in ("target_signature", "elaborated_type")
        )
    )
    shared_symbols = sorted(source_symbols & target_symbols)
    if shared_symbols:
        bonus = min(0.18, 0.10 + 0.02 * (len(shared_symbols) - 1))
        score += bonus
        reasons.append(
            "compiler/elaborator interface symbols "
            + ", ".join(shared_symbols[:4])
        )
    # Interpretations are commonly represented by a target package plus
    # declarations in a namespace owned by that package.
    if source.get("kind") in {
        "sublocale", "interpretation", "global_interpretation"
    }:
        qualified_parts = {
            _normalized_name(part)
            for part in str(target.get("qualified_name", "")).split(".")[:-1]
        }
        if source_normalized and source_normalized in qualified_parts:
            score += 0.40
            reasons.append("interpretation namespace owner")
    # These are ranking weights, not probabilities. Saturating at 1.0 erases
    # module/context evidence and can turn a generic declaration into a tie
    # with an unrelated specialization.
    return score, reasons


def match_items(
    source_index: dict[str, Any],
    target_index: dict[str, Any],
    *,
    threshold: float = 0.60,
) -> dict[str, Any]:
    sources = source_index.get("declarations", [])
    targets = target_index.get("declarations", [])
    source_by_id = {item["id"]: item for item in sources}
    target_by_id = {item["id"]: item for item in targets}
    all_candidates: dict[str, list[dict[str, Any]]] = {}
    edges: list[tuple[float, str, str, list[str]]] = []
    for source in sources:
        candidates = []
        for target in targets:
            if not target.get("match_eligible", target.get("judge_eligible", True)):
                continue
            if target.get("match_only") and source.get("kind") != "Parameter":
                continue
            score, reasons = _match_score(source, target)
            if score >= 0.35:
                candidates.append(
                    {
                        "target_id": target["id"],
                        "score": round(score, 6),
                        "reasons": reasons,
                    }
                )
            if score >= threshold:
                edges.append((score, source["id"], target["id"], reasons))
        all_candidates[source["id"]] = sorted(
            candidates, key=lambda item: (-item["score"], item["target_id"])
        )[:5]

    used_sources: set[str] = set()
    used_targets: set[str] = set()
    primary_source_by_target: dict[str, str] = {}
    matches: list[dict[str, Any]] = []
    sorted_edges = sorted(
        edges, key=lambda item: (-item[0], item[1], item[2])
    )

    def add_match(
        score: float,
        source_id: str,
        target_id: str,
        reasons: list[str],
        *,
        target_reused: bool,
    ) -> None:
        used_sources.add(source_id)
        used_targets.add(target_id)
        if not target_reused:
            primary_source_by_target[target_id] = source_id
        match = {
            "source_id": source_id,
            "target_id": target_id,
            "score": round(score, 6),
            "method": (
                "deterministic_name_role_target_reuse"
                if target_reused
                else "deterministic_name_role"
            ),
            "reasons": reasons,
            "alternatives": [
                item
                for item in all_candidates[source_id]
                if item["target_id"] != target_id
            ],
        }
        # Keep the legacy primary-match payload byte-stable so an unrelated
        # matcher improvement does not invalidate hundreds of cached prompts.
        if target_reused:
            match["target_reused"] = True
        matches.append(match)

    # Preserve the strongest distinct source/target assignments first.  This
    # prevents a merely similar implementation declaration from displacing an
    # exact-name proof declaration for another source item.
    for score, source_id, target_id, reasons in sorted_edges:
        if source_id in used_sources or target_id in used_targets:
            continue
        source = source_by_id[source_id]
        target = target_by_id[target_id]
        source_stem = _normalized_name(Path(source["source_file"]).stem)
        target_namespace = {
            _normalized_name(part)
            for part in target.get("qualified_name", target["name"]).split(".")[:-1]
        }
        same_module = source_stem == _normalized_name(
            Path(target["target_file"]).stem
        )
        exact_namespaced_item = (
            source_stem in target_namespace
            and _normalized_name(source["name"]) == _normalized_name(target["name"])
        )
        if (
            source_id not in target.get("annotated_source_ids", [])
            and not same_module
            and not exact_namespaced_item
        ):
            continue
        add_match(
            score,
            source_id,
            target_id,
            reasons,
            target_reused=False,
        )

    # A translated repository may intentionally deduplicate source-identical
    # declarations from different modules.  Give only still-unmatched sources
    # a second chance to point at an already assigned target.  Fail closed
    # unless the target explicitly names the source or the source interfaces
    # are identical; name similarity alone cannot justify target reuse.
    for score, source_id, target_id, reasons in sorted_edges:
        if source_id in used_sources:
            continue
        if target_id not in primary_source_by_target:
            continue
        source = source_by_id[source_id]
        primary = source_by_id[primary_source_by_target[target_id]]
        signature = normalize_space(str(source.get("source_signature") or ""))
        identical_source = bool(signature) and (
            _normalized_name(source["name"]) == _normalized_name(primary["name"])
            and _source_role(source["kind"]) == _source_role(primary["kind"])
            and signature
            == normalize_space(str(primary.get("source_signature") or ""))
            and source.get("type_signature") == primary.get("type_signature")
            and source.get("context", source.get("section_context", []))
            == primary.get("context", primary.get("section_context", []))
        )
        if (
            source_id not in target_by_id[target_id].get("annotated_source_ids", [])
            and not identical_source
        ):
            continue
        add_match(
            score,
            source_id,
            target_id,
            reasons,
            target_reused=target_id in used_targets,
        )
    source_ids = {item["id"] for item in sources}
    target_ids = {
        item["id"]
        for item in targets
        if not item.get("match_only")
        and item.get("unmatched_eligible", item.get("judge_eligible", True))
    }
    return {
        "threshold": threshold,
        "matches": sorted(matches, key=lambda item: item["source_id"]),
        "unmatched_source_ids": sorted(source_ids - used_sources),
        "unmatched_target_ids": sorted(target_ids - used_targets),
        "candidate_matches": all_candidates,
    }


def _job_key(kind: str, source_id: str | None, target_id: str | None) -> str:
    payload = json.dumps(
        [kind, source_id, target_id], ensure_ascii=False, separators=(",", ":")
    )
    return sha256_bytes(payload.encode("utf-8"))[:20]


def make_judge_plan(
    task: TaskConfig,
    source_index: dict[str, Any],
    target_index: dict[str, Any],
    *,
    threshold: float = 0.60,
    prompt_version: str = PROMPT_VERSION,
) -> dict[str, Any]:
    if prompt_version not in SUPPORTED_PROMPT_VERSIONS:
        raise PipelineError(
            f"unsupported judge prompt version: {prompt_version}"
        )
    matching = match_items(source_index, target_index, threshold=threshold)
    source_graph = build_source_dependency_graph(source_index)
    target_graph = dependency_graph(
        [item["id"] for item in target_index["declarations"]],
        {
            item["id"]: item.get("dependencies", [])
            for item in target_index["declarations"]
        },
    )
    layer_by_source = {
        source_id: layer
        for layer, source_ids in enumerate(source_graph["topological_layers"])
        for source_id in source_ids
    }
    jobs: list[dict[str, Any]] = []
    for match in matching["matches"]:
        jobs.append(
            {
                "key": _job_key("matched", match["source_id"], match["target_id"]),
                "kind": "matched",
                "source_language": task.source.language,
                "source_id": match["source_id"],
                "target_id": match["target_id"],
                "dependency_layer": layer_by_source.get(match["source_id"]),
                "matcher": match,
            }
        )
    for source_id in matching["unmatched_source_ids"]:
        jobs.append(
            {
                "key": _job_key("source_unmatched", source_id, None),
                "kind": "source_unmatched",
                "source_language": task.source.language,
                "source_id": source_id,
                "target_id": None,
                "dependency_layer": layer_by_source.get(source_id),
                "matcher": {
                    "alternatives": matching["candidate_matches"].get(source_id, [])
                },
            }
        )
    for target_id in matching["unmatched_target_ids"]:
        jobs.append(
            {
                "key": _job_key("target_unmatched", None, target_id),
                "kind": "target_unmatched",
                "source_language": task.source.language,
                "source_id": None,
                "target_id": target_id,
                "dependency_layer": None,
                "matcher": None,
            }
        )
    jobs.sort(
        key=lambda item: (
            item["dependency_layer"]
            if item["dependency_layer"] is not None
            else 10**9,
            item["kind"],
            item["key"],
        )
    )
    return {
        "version": JUDGE_VERSION,
        "prompt_version": prompt_version,
        "task_id": task.task_id,
        "source_index_sha256": sha256_json(source_index),
        "target_index_sha256": sha256_json(target_index),
        "source_dependency_graph": source_graph,
        "target_dependency_graph": target_graph,
        "matching": matching,
        "job_count": len(jobs),
        "jobs": jobs,
    }


def _truncate(value: str | None, limit: int = 24000) -> str | None:
    if value is None or len(value) <= limit:
        return value
    return value[:limit] + f"\n... [truncated {len(value) - limit} characters]"


def _source_payload(
    item: dict[str, Any] | None,
    *,
    include_proof_using: bool = False,
    include_compiler_surface: bool = False,
) -> dict[str, Any] | None:
    if item is None:
        return None
    payload = {
        "id": item["id"],
        "language": item.get("language"),
        "name": item["name"],
        "qualified_name": item.get("fully_qualified_name")
        or item.get("qualified_name", item["name"]),
        "kind": item["kind"],
        "file": item["source_file"],
        "line": item["source_line"],
        "module": item.get("module"),
        "module_path": item.get("module_path", []),
        "attributes": item.get("attributes", []),
        "visibility": item.get("visibility", "public"),
        "metadata": item.get("metadata", {}),
        "context": item.get("context", []),
        "section_context": item.get("section_context", []),
        "signature": item.get("source_signature"),
        "type_signature": item.get("type_signature"),
        "source_span": item.get("source_span"),
        "proof": _truncate(item.get("proof")),
        "program_obligations": [
            _truncate(value) for value in item.get("program_obligations", [])
        ],
        "dependencies": item.get("judge_dependencies", item.get("dependencies", [])),
    }
    if include_proof_using:
        if item.get("default_proof_using"):
            payload["default_proof_using"] = item["default_proof_using"]
        if item.get("proof_using"):
            payload["proof_using"] = item["proof_using"]
    if include_compiler_surface:
        # Isabelle datatype/quotient commands elaborate one explicit outer
        # declaration into constructors, discriminators, selectors, relators,
        # and recursors.  Those are observable source semantics, but the raw
        # export also contains hundreds of BNF/Quickcheck implementation
        # artifacts.  Give the judge a bounded compiler-backed public surface
        # instead of either hiding it or flooding the prompt with internals.
        payload["compiler_declared_surface"] = _compiler_declared_surface(item)
        payload["compiler_rule_surface"] = _compiler_rule_surface(item)
        payload["type_compiler_category"] = item.get("type_compiler_category")
        payload["type_compiler_entity"] = item.get("type_compiler_entity")
    return payload


def _compiler_declared_surface(item: dict[str, Any] | None) -> list[dict[str, Any]]:
    if item is None:
        return []
    excluded_prefixes = (
        "Abs_", "Rep_", "alg_", "ctor_", "dtor_", "equal_",
        "full_exhaustive_", "map_pre_", "min_alg_", "mor_", "narrowing_",
        "partial_term_", "pred_pre_", "random_", "rel_pre_", "set1_pre_",
        "set2_pre_", "size_", "str_", "term_of_", "typerep_", "wit_",
        "wit_pre_",
    )
    surface = []
    seen: set[str] = set()
    interpretation_prefix = (
        str(item.get("name", "")).split(".")[-1] + "."
        if item.get("kind")
        in {"sublocale", "interpretation", "global_interpretation"}
        else None
    )
    for entity in item.get("compiler_entities", []):
        xname = str(entity.get("xname", ""))
        if (
            not xname
            or xname in seen
            or (
                "." in xname
                and not (
                    interpretation_prefix
                    and xname.startswith(interpretation_prefix)
                    and xname.count(".") == 1
                )
            )
            or xname.startswith(excluded_prefixes)
            or (
                item.get("kind") in {"datatype", "nominal_datatype"}
                and (
                    "_pre_" in xname
                    or xname.startswith("set_pre_")
                )
            )
        ):
            continue
        if entity.get("category") not in {"const", "type", "locale"}:
            continue
        surface.append(
            {
                "category": entity.get("category"),
                "name": xname,
                "qualified_name": entity.get("fully_qualified_name"),
                "type_signature": _truncate(entity.get("type_signature"), limit=1200),
            }
        )
        seen.add(xname)
        if len(surface) == 48:
            break
    return surface


def _compiler_rule_surface(item: dict[str, Any] | None) -> list[dict[str, Any]]:
    """Expose the small rule family that determines a compiler-selected item.

    Isabelle can export a locale-defined inductive constant without the locale
    predicate while attaching that predicate to generated convenience rules.
    Keeping only the raw constant hides this distinction from the judge; keeping
    every theorem floods the prompt.  Select the definition equation and the
    immediate generated rule family, with dependency names as a compact,
    compiler-backed account of which rules retain ambient context. Presence in
    Export_Theory does not by itself prove that an internal package theorem is
    addressable as a public Isabelle fact, so retain the external name and make
    that visibility boundary explicit to the judge.
    """
    if item is None:
        return []
    primary = str(item.get("type_compiler_entity") or "")
    if not primary:
        return []
    definition_name = primary + "_def"
    surface: list[dict[str, Any]] = []
    seen: set[tuple[str, str]] = set()
    for entity in item.get("compiler_entities", []):
        category = str(entity.get("category") or "")
        qualified_name = str(entity.get("fully_qualified_name") or "")
        if category not in {"axiom", "thm"} or not (
            qualified_name == definition_name
            or qualified_name.startswith(primary + ".")
        ):
            continue
        key = (category, qualified_name)
        if key in seen:
            continue
        seen.add(key)
        surface.append(
            {
                "category": category,
                "qualified_name": qualified_name,
                "external_name": entity.get("xname"),
                "source_visibility": entity.get(
                    "source_visibility", "compiler_exported_not_name_validated"
                ),
                "external_name_compiler_validated": entity.get(
                    "external_name_compiler_validated", False
                ),
                "role": (
                    "definition_equation"
                    if qualified_name == definition_name
                    else "generated_rule"
                ),
                "dependencies": entity.get("dependencies", []),
                "type_signature": _truncate(
                    entity.get("type_signature"), limit=1600
                ),
            }
        )
        if len(surface) == 12:
            break
    return surface


def _target_payload(
    item: dict[str, Any] | None,
    *,
    include_environment: bool = False,
) -> dict[str, Any] | None:
    if item is None:
        return None
    payload = {
        "id": item["id"],
        "name": item["name"],
        "kind": item["kind"],
        "role": item["role"],
        "file": item["target_file"],
        "line": item["target_line"],
        "signature": item["target_signature"],
        "text": _truncate(item["target_text"]),
        "dependencies": item.get("dependencies", []),
    }
    if include_environment:
        payload.update(
            {
                "qualified_name": item.get("qualified_name"),
                "environment_confirmed": item.get(
                    "environment_confirmed", False
                ),
                "environment_kind": item.get("environment_kind"),
                "elaborated_type": item.get("elaborated_type"),
                "environment_unsafe": item.get("environment_unsafe"),
                "environment_partial": item.get("environment_partial"),
            }
        )
    return payload


def _indexed_subjects(item: dict[str, Any] | None) -> set[str]:
    """Return declaration spellings backed by the normalized compiler index."""
    if not item:
        return set()
    compiler_subject = item.get("type_compiler_entity")
    qualified_subjects = () if compiler_subject else (
        item.get("fully_qualified_name"),
        item.get("qualified_name"),
    )
    subjects = {
        str(value)
        for value in (
            compiler_subject,
            *qualified_subjects,
            item.get("name"),
        )
        if value
    }
    name = item.get("name")
    module = item.get("module")
    if name and module and not compiler_subject:
        subjects.add(f"{module}.{name}")
    module_path = item.get("module_path") or []
    if name and module_path and not compiler_subject:
        subjects.add(
            ".".join([*(str(value) for value in module_path), str(name)])
        )
    return subjects


def _preferred_indexed_subject(item: dict[str, Any] | None) -> str:
    if not item:
        return "unavailable-unmatched-subject"
    for value in (
        item.get("type_compiler_entity"),
        item.get("fully_qualified_name"),
        item.get("qualified_name"),
    ):
        if value:
            return str(value)
    name = item.get("name")
    module = item.get("module")
    if name and module:
        return f"{module}.{name}"
    if name:
        return str(name)
    return "unavailable-unmatched-subject"


_SCOPE_KEYWORDS = {
    "and", "by", "decide", "else", "end", "false", "if", "in", "match",
    "not", "or", "then", "true", "with",
}


def _scope_dependencies(expression: str, item: dict[str, Any]) -> list[str]:
    excluded = {
        str(item.get("name", "")),
        *(str(value).split(".")[-1] for value in item.get("dependencies", [])),
    }
    return sorted(
        {
            token
            for token in re.findall(r"\b[A-Za-z_][A-Za-z_0-9']*\b", expression)
            if token[0].islower()
            and token not in _SCOPE_KEYWORDS
            and token not in excluded
        }
    )[:8]


def _canonical_scope_guard(value: str) -> str:
    value = normalize_space(value).strip("() ")
    prefix = re.fullmatch(
        r"Z(?P<op>le|lt|ge|gt|eq)_bool\s+(?P<left>-?\d+|[A-Za-z_]\w*)\s+"
        r"(?P<right>-?\d+|[A-Za-z_]\w*)",
        value,
    )
    if prefix:
        operator = {"le": "<=", "lt": "<", "ge": ">=", "gt": ">", "eq": "="}[
            prefix.group("op")
        ]
        return f"{prefix.group('left')} {operator} {prefix.group('right')}"
    return (
        value.replace("<>", "!=")
        .replace("≤", "<=")
        .replace("≥", ">=")
        .replace("≠", "!=")
    )


def _scope_boundaries(expression: str) -> dict[str, list[int]]:
    values: dict[str, set[int]] = defaultdict(set)
    normalized = _canonical_scope_guard(expression)
    patterns = (
        r"\b(?P<name>[a-z][A-Za-z_0-9']*)\s*(?:<=|>=|<|>|=|!=|<>)\s*(?P<n>-?\d+)",
        r"(?P<n>-?\d+)\s*(?:<=|>=|<|>|=|!=|<>)\s*\b(?P<name>[a-z][A-Za-z_0-9']*)",
    )
    for pattern in patterns:
        for match in re.finditer(pattern, normalized):
            boundary = int(match.group("n"))
            values[match.group("name")].update((boundary - 1, boundary, boundary + 1))
    return {name: sorted(candidates) for name, candidates in sorted(values.items())}


_BINDER_RE = re.compile(
    r"(?P<open>[([{])\s*(?P<names>[A-Za-z_][A-Za-z_0-9']*(?:\s+[A-Za-z_][A-Za-z_0-9']*)*)"
    r"\s*:\s*(?P<type>[^)\]}\n]+)[)\]}]"
)


def _compiler_interface(item: dict[str, Any] | None, side: str) -> tuple[str, bool]:
    if not item:
        return "", False
    if side == "source":
        compiled = str(item.get("type_signature") or "").strip()
        if compiled:
            return compiled, True
        lexical = "\n".join(
            [
                *(str(value) for value in item.get("section_context", [])),
                str(item.get("source_signature") or ""),
            ]
        )
        return lexical, False
    compiled = str(item.get("elaborated_type") or "").strip()
    if compiled:
        return compiled, bool(item.get("environment_confirmed", True))
    return str(item.get("target_signature") or item.get("target_text") or ""), False


def _binder_inventory(interface: str) -> list[dict[str, Any]]:
    binders: list[dict[str, Any]] = []
    for match in _BINDER_RE.finditer(interface):
        binder_type = normalize_space(match.group("type"))
        proof = match.group("open") == "[" or (
            match.group("open") == "{" and bool(
            re.search(
                r"(?:\bFact\b|\bValid[A-Za-z_]*\b|\bMonotone[A-Za-z_]*\b|"
                r"(?:<>|!=|≠|<=|>=|≤|≥|<|>|=))",
                binder_type,
            )
            )
        )
        for name in match.group("names").split():
            binders.append(
                {
                    "name": name,
                    "type": binder_type,
                    "role": "proof_or_instance" if proof else "semantic_input",
                    "implicit": match.group("open") != "(",
                }
            )
    if not binders and "∀" not in interface and not re.search(r"\bforall\b", interface):
        depth = 0
        start = 0
        domains: list[str] = []
        index = 0
        while index < len(interface):
            character = interface[index]
            if character in "([{":
                depth += 1
            elif character in ")]}":
                depth = max(0, depth - 1)
            arrow_length = (
                1 if character == "→" else 2 if interface[index : index + 2] == "->" else 0
            )
            if depth == 0 and arrow_length:
                domains.append(normalize_space(interface[start:index]))
                start = index + arrow_length
                index += arrow_length
                continue
            index += 1
        binders.extend(
            {
                "name": f"arg{offset}",
                "type": domain,
                "role": "semantic_input",
                "implicit": False,
            }
            for offset, domain in enumerate(domains, start=1)
            if domain
        )
    return binders


def _normalized_type(value: str) -> str:
    value = normalize_space(value).replace("ℝ", "Real").replace("ℤ", "Int")
    value = re.sub(r"(?<![A-Za-z0-9_'])R(?![A-Za-z0-9_'])", "Real", value)
    value = re.sub(r"(?<![A-Za-z0-9_'])Z(?![A-Za-z0-9_'])", "Int", value)
    return value.replace("→", "->")


def _interface_analysis(
    source_item: dict[str, Any] | None,
    target_item: dict[str, Any] | None,
) -> dict[str, Any]:
    source_interface, source_compiled = _compiler_interface(source_item, "source")
    target_interface, target_compiled = _compiler_interface(target_item, "target")
    source_binders = _binder_inventory(source_interface)
    target_binders = _binder_inventory(target_interface)
    source_by_name = {item["name"]: item for item in source_binders}
    target_by_name = {item["name"]: item for item in target_binders}
    compiler_validated = source_compiled and target_compiled
    warnings: list[dict[str, Any]] = []

    def warning(
        warning_id: str,
        kind: str,
        depends_on: list[str],
        region: str,
        explanation: str,
        *,
        witness: dict[str, Any] | None = None,
    ) -> None:
        warnings.append(
            {
                "id": warning_id,
                "kind": kind,
                "severity": "advisory",
                "authority": "heuristic_feedback",
                "compiler_validated": compiler_validated,
                "depends_on": depends_on,
                "domain_region": region,
                "two_sided_behavioral_witness_possible": kind
                not in {"source_domain_loss", "target_domain_extension"},
                "suggested_failure_category": kind,
                "witness": witness,
                "explanation": explanation,
            }
        )

    refinement_models = {
        "radix": ("Int", "1", "source invariant requires radix >= 2"),
        "positive": ("Int", "0", "source positive type excludes zero"),
        "N": ("Int", "-1", "source nonnegative type excludes negative integers"),
        "nat": ("Int", "-1", "source natural type excludes negative integers"),
    }
    for name in sorted(source_by_name.keys() & target_by_name.keys()):
        source_type = source_by_name[name]["type"]
        target_type = target_by_name[name]["type"]
        source_norm = _normalized_type(source_type)
        target_norm = _normalized_type(target_type)
        matched_refinement = False
        for refined, (primitive, model, reason) in refinement_models.items():
            if re.search(rf"(?:^|\.){re.escape(refined)}$", source_type) and primitive in target_norm:
                matched_refinement = True
                warning(
                    f"target-domain-extension:{name}",
                    "target_domain_extension",
                    [name],
                    f"not WF_source({name}) and WF_target({name})",
                    f"Target binder {name} : {target_type} drops the source refinement "
                    f"{name} : {source_type}; {reason}.",
                    witness={"assignment": {name: model}, "source": "uninhabited", "target": "inhabited"},
                )
                break
        if (
            not matched_refinement
            and source_by_name[name]["role"] == "semantic_input"
            and target_by_name[name]["role"] == "semantic_input"
            and source_norm != target_norm
        ):
            warning(
                f"interface-relation:{name}",
                "interface_relation_failure",
                [name],
                f"WF_source({name}) and WF_target({name})",
                f"No compiler-visible representation relation equates source binder "
                f"{name} : {source_type} with target binder {name} : {target_type}.",
            )

    source_normalized = _canonical_scope_guard(source_interface)
    for binder in target_binders:
        if binder["role"] != "proof_or_instance" or not re.search(
            r"(?:<>|!=|≠|<=|>=|≤|≥|<|>|=)", binder["type"]
        ):
            continue
        constraint = _canonical_scope_guard(binder["type"])
        if constraint in source_normalized:
            continue
        depends_on = _scope_dependencies(constraint, target_item or {})
        if (
            constraint in {"1 < beta", "2 <= beta"}
            and source_by_name.get("beta", {}).get("type", "").endswith("radix")
        ):
            continue
        warning(
            f"source-domain-loss:{binder['name']}",
            "source_domain_loss",
            depends_on,
            f"WF_source({','.join(depends_on)}) and not WF_target({','.join(depends_on)})",
            f"Target proof binder {binder['name']} : {binder['type']} has no corresponding "
            "compiler-visible source-domain constraint.",
            witness={"boundary_values": _scope_boundaries(constraint)},
        )

    source_values = [item for item in source_binders if item["role"] == "semantic_input"]
    target_values = [item for item in target_binders if item["role"] == "semantic_input"]
    if source_values and target_values and len(source_values) != len(target_values):
        warning(
            "semantic-arity-mismatch",
            "interface_relation_failure",
            sorted({item["name"] for item in [*source_values, *target_values]}),
            "WF_source(inputs) and WF_target(inputs)",
            f"Compiler interfaces expose {len(source_values)} source semantic binders and "
            f"{len(target_values)} target semantic binders after proof/typeclass filtering.",
        )

    source_only = [item for item in warnings if item["kind"] == "source_domain_loss"]
    target_only = [item for item in warnings if item["kind"] == "target_domain_extension"]
    return {
        "source": {
            "interface": source_interface,
            "compiler_validated": source_compiled,
            "binders": source_binders,
            "authority": "heuristic_feedback",
        },
        "target": {
            "interface": target_interface,
            "compiler_validated": target_compiled,
            "binders": target_binders,
            "authority": "heuristic_feedback",
        },
        "decision_policy": (
            "Both sides are symmetric heuristic feedback for the judge LLM. "
            "Neither warnings nor compiler_validated flags determine the verdict."
        ),
        "compiler_warnings": warnings,
        "domain_partition": {
            "shared": "WF_source(a) and WF_target(a)",
            "source_only": [item["domain_region"] for item in source_only],
            "target_only": [item["domain_region"] for item in target_only],
            "behavioral_counterexample_search_region": "WF_source(a) and WF_target(a)",
        },
        "scope_comparison": {
            "source_scope": "WF_source(a)",
            "target_scope": "WF_target(a)",
            "candidate_relation": (
                "target_scope_strict_subset"
                if source_only
                else "source_scope_strict_subset"
                if target_only
                else "undetermined"
            ),
            "authority": "heuristic_feedback",
            "decision_owner": "judge_llm",
        },
        "typed_witness_plan": {
            "abstract_inputs": sorted(
                {item["name"] for item in [*source_values, *target_values]}
            ),
            "source_application_template": " ".join(
                [
                    _preferred_indexed_subject(source_item),
                    *(f"{{{{{item['name']}}}}}" for item in source_binders),
                ]
            ),
            "target_application_template": " ".join(
                [
                    _preferred_indexed_subject(target_item),
                    *(f"{{{{{item['name']}}}}}" for item in target_binders),
                ]
            ),
            "trust_boundary": "native elaboration and compiler replay",
        },
    }


def attach_relational_dependency_context(
    source_by_id: dict[str, dict[str, Any]],
    target_by_id: dict[str, dict[str, Any]],
    *,
    max_depth: int = 4,
    max_items: int = 16,
) -> None:
    """Attach a bounded compiler-resolved dependency slice to prompt items."""
    for side, index in (("source", source_by_id), ("target", target_by_id)):
        for root in index.values():
            queue = [
                (dependency, 1)
                for dependency in (
                    root.get("dependency_ids", [])
                    if side == "source"
                    else root.get("dependencies", [])
                )
                if dependency in index
            ]
            seen: set[str] = set()
            summaries = []
            while queue and len(summaries) < max_items:
                dependency_id, depth = queue.pop(0)
                if dependency_id in seen or depth > max_depth:
                    continue
                seen.add(dependency_id)
                dependency = index[dependency_id]
                summaries.append(
                    {
                        "id": dependency_id,
                        "name": dependency.get("name"),
                        "kind": dependency.get("kind"),
                        "depth": depth,
                        "source_signature": dependency.get("source_signature"),
                        "type_signature": dependency.get("type_signature"),
                        "target_text": dependency.get("target_text"),
                        "target_signature": dependency.get("target_signature"),
                        "elaborated_type": dependency.get("elaborated_type"),
                        "environment_confirmed": dependency.get("environment_confirmed"),
                        "native_symbolic": dependency.get("native_symbolic"),
                    }
                )
                next_ids = (
                    dependency.get("dependency_ids", [])
                    if side == "source"
                    else dependency.get("dependencies", [])
                )
                queue.extend((value, depth + 1) for value in next_ids if value in index)
            root["relational_dependencies"] = summaries


_SYMBOLIC_NUMERIC_GUARD_RE = re.compile(
    r"(?:\b[a-z][A-Za-z_0-9']*\s*(?:<=|>=|<|>|=|!=|<>|≤|≥|≠)\s*-?\d+|"
    r"-?\d+\s*(?:<=|>=|<|>|=|!=|<>|≤|≥|≠)\s*\b[a-z][A-Za-z_0-9']*)"
)


def _boundary_assignments(
    boundaries: dict[str, list[int]], *, max_assignments: int = 32
) -> list[dict[str, int]]:
    assignments: list[dict[str, int]] = [{}]
    for name, values in sorted(boundaries.items()):
        expanded = []
        for assignment in assignments:
            for value in values:
                expanded.append({**assignment, name: value})
                if len(expanded) == max_assignments:
                    break
            if len(expanded) == max_assignments:
                break
        assignments = expanded
        if len(assignments) == max_assignments:
            break
    return assignments if boundaries else []


def _symbolic_paths(item: dict[str, Any] | None, side: str) -> dict[str, Any]:
    """Expose compiler-native symbolic branch artifacts and boundary probes."""
    if not item:
        return {
            "paths": [], "branches": [], "boundary_values": {},
            "boundary_candidates": [], "dependency_slice": [],
        }

    declarations = [{"id": item.get("id"), "name": item.get("name"), "depth": 0,
                     "native_symbolic": item.get("native_symbolic")}]
    dependency_slice = []
    for dependency in item.get("relational_dependencies", [])[:16]:
        native = dependency.get("native_symbolic") or {}
        dependency_slice.append(
            {
                "id": dependency.get("id"),
                "name": dependency.get("name"),
                "kind": dependency.get("kind"),
                "depth": dependency.get("depth"),
                "summary": "native_expanded" if native.get("branches") else "interface_only",
                "engine": native.get("engine"),
            }
        )
        declarations.append(
            {
                "id": dependency.get("id"),
                "name": dependency.get("name"),
                "depth": dependency.get("depth"),
                "native_symbolic": native,
            }
        )

    paths: list[dict[str, Any]] = []
    branches: list[dict[str, Any]] = []
    boundaries: dict[str, set[int]] = defaultdict(set)
    for declaration in declarations:
        native = declaration.get("native_symbolic") or {}
        for native_branch in native.get("branches", [])[:64]:
            statement = str(native_branch.get("type") or native_branch.get("term") or "")
            branch = {
                "id": native_branch.get("name") or f"{declaration.get('name')}:native-{len(branches) + 1}",
                "declaration_id": declaration.get("id"),
                "declaration_name": declaration.get("name"),
                "declaration_depth": declaration.get("depth"),
                "engine": native.get("engine"),
                "native_statement": statement,
            }
            branches.append(branch)
            for match in _SYMBOLIC_NUMERIC_GUARD_RE.finditer(statement):
                predicate = _canonical_scope_guard(match.group(0))
                boundary_values = _scope_boundaries(predicate)
                for name, candidates in boundary_values.items():
                    boundaries[name].update(candidates)
                paths.append(
                    {
                        "kind": "native_numeric_constraint",
                        "predicate": predicate,
                        "declaration_name": declaration.get("name"),
                        "native_branch": branch["id"],
                        "depends_on": _scope_dependencies(predicate, item),
                        "regions": [predicate, f"not ({predicate})"],
                        "authority": "candidate_boundary_only",
                        "boundary_values": boundary_values,
                    }
                )

    boundary_values = {
        name: sorted(values)[:8] for name, values in sorted(boundaries.items())
    }
    return {
        "paths": paths,
        "branches": branches,
        "path_regions": [entry["native_statement"] for entry in branches],
        "boundary_values": boundary_values,
        "boundary_candidates": _boundary_assignments(boundary_values),
        "dependency_slice": dependency_slice,
        "analysis_limits": {
            "dependency_depth": 4,
            "dependency_items": 16,
            "native_branches_per_declaration": 64,
        },
    }


def derive_counterexample_search_scope(
    source_item: dict[str, Any] | None,
    target_item: dict[str, Any] | None,
) -> dict[str, Any]:
    """Conservatively partition executable paths without making semantic claims."""
    source = _symbolic_paths(source_item, "source")
    target = _symbolic_paths(target_item, "target")
    source_guards = {entry["predicate"]: entry for entry in source["paths"]}
    target_guards = {entry["predicate"]: entry for entry in target["paths"]}
    scopes = []
    for origin, guards, other in (
        ("source_only", source_guards, target_guards),
        ("target_only", target_guards, source_guards),
    ):
        for predicate in sorted(guards.keys() - other.keys()):
            scopes.append(
                {
                    "origin": origin,
                    "predicate": predicate,
                    "depends_on": guards[predicate]["depends_on"],
                    "regions_to_compare": guards[predicate]["regions"],
                }
            )
    source_text = str((source_item or {}).get("source_signature") or "")
    target_text = str(
        (target_item or {}).get("target_text")
        or (target_item or {}).get("target_signature")
        or ""
    )
    source_rnd = re.search(r"\brnd\s*:\s*([^,\)\n]+)", source_text)
    target_rnd = re.search(r"\brnd\s*:\s*([^,\)\n]+)", target_text)
    if source_rnd and target_rnd:
        source_type = normalize_space(source_rnd.group(1))
        target_type = normalize_space(target_rnd.group(1))
        if source_type != target_type:
            scopes.insert(
                0,
                {
                    "origin": "cross_interface",
                    "predicate": f"rnd representation: {source_type} versus {target_type}",
                    "depends_on": [
                        name
                        for name in ("rnd", "x")
                        if re.search(rf"\b{name}\b", source_text)
                        and re.search(rf"\b{name}\b", target_text)
                    ],
                    "regions_to_compare": [
                        "same non-integral input with floor/truncation mode",
                        "same non-integral input with ceiling mode",
                    ],
                    "probe_values": {
                        "x": ["3/5", "3/2"],
                        "rnd": ["floor_or_truncation", "ceiling"],
                    },
                },
            )
    interface = _interface_analysis(source_item, target_item)
    return {
        "method": "compiler-native symbolic reduction/equation extraction with boundary probes",
        "source": source,
        "target": target,
        "candidate_misalignment_scopes": scopes[:16],
        "boundary_candidates": _boundary_assignments(
            {
                name: sorted(values)[:8]
                for name, values in sorted(
                    {
                        key: set(source["boundary_values"].get(key, []))
                        | set(target["boundary_values"].get(key, []))
                        for key in set(source["boundary_values"]) | set(target["boundary_values"])
                    }.items()
                )
            }
        ),
        "compiler_interface_analysis": interface,
        "compiler_warnings": interface["compiler_warnings"],
        "domain_partition": interface["domain_partition"],
        "scope_comparison": interface["scope_comparison"],
        "typed_witness_plan": interface["typed_witness_plan"],
        "evidence_taxonomy": [
            "behavioral_counterexample",
            "source_domain_loss",
            "target_domain_extension",
            "interface_relation_failure",
        ],
        "limitation": (
            "Compiler-native branch artifacts are heuristic inputs; native reducers may leave "
            "opaque terms and every candidate still requires native evidence validation."
        ),
    }


def render_judge_prompt(
    task: TaskConfig,
    job: dict[str, Any],
    source_item: dict[str, Any] | None,
    target_item: dict[str, Any] | None,
    *,
    prompt_version: str = PROMPT_VERSION,
) -> str:
    if prompt_version not in SUPPORTED_PROMPT_VERSIONS:
        raise PipelineError(
            f"unsupported judge prompt version: {prompt_version}"
        )
    payload = {
        "job": job,
        "source_item": _source_payload(
            source_item,
            include_proof_using=prompt_version
            in {
                "semantic-alignment-v2",
                "semantic-alignment-v3",
                "semantic-alignment-v4",
                "semantic-alignment-v5",
                "semantic-alignment-v6",
                "semantic-alignment-v7",
                "semantic-alignment-v8",
                "semantic-alignment-v9",
                "semantic-alignment-v10",
                "semantic-alignment-v11",
                "semantic-alignment-v12",
                "semantic-alignment-v13",
                "semantic-alignment-v21",
                "semantic-alignment-v22",
                "semantic-alignment-v23",
                "semantic-alignment-v24",
                "semantic-alignment-v25",
                "semantic-alignment-v26",
                "semantic-alignment-v27",
            },
            include_compiler_surface=prompt_version
            in {
                "semantic-alignment-v5",
                "semantic-alignment-v6",
                "semantic-alignment-v7",
                "semantic-alignment-v8",
                "semantic-alignment-v9",
                "semantic-alignment-v10",
                "semantic-alignment-v11",
                "semantic-alignment-v12",
                "semantic-alignment-v13",
                "semantic-alignment-v21",
                "semantic-alignment-v22",
                "semantic-alignment-v23",
                "semantic-alignment-v24",
                "semantic-alignment-v25",
                "semantic-alignment-v26",
                "semantic-alignment-v27",
            },
        ),
        "target_item": _target_payload(
            target_item,
            include_environment=prompt_version
            in {
                "semantic-alignment-v3",
                "semantic-alignment-v4",
                "semantic-alignment-v5",
                "semantic-alignment-v6",
                "semantic-alignment-v7",
                "semantic-alignment-v8",
                "semantic-alignment-v9",
                "semantic-alignment-v10",
                "semantic-alignment-v11",
                "semantic-alignment-v12",
                "semantic-alignment-v13",
                "semantic-alignment-v21",
                "semantic-alignment-v22",
                "semantic-alignment-v23",
                "semantic-alignment-v24",
                "semantic-alignment-v25",
                "semantic-alignment-v26",
                "semantic-alignment-v27",
            },
        ),
    }
    if prompt_version in {
        "semantic-alignment-v14",
        "semantic-alignment-v15",
        "semantic-alignment-v16",
        "semantic-alignment-v20",
        "semantic-alignment-v21",
        "semantic-alignment-v22",
        "semantic-alignment-v23",
        "semantic-alignment-v24",
        "semantic-alignment-v25",
        "semantic-alignment-v26",
        "semantic-alignment-v27",
    }:
        payload["counterexample_search_scope"] = derive_counterexample_search_scope(
            source_item, target_item
        )
    source_language = task.source.language
    source_subject = _preferred_indexed_subject(source_item)
    target_subject = _preferred_indexed_subject(target_item)
    source_import_guidance = ""
    if source_language == "isabelle" and source_item:
        theory = str(
            (source_item.get("metadata") or {}).get("theory")
            or source_item.get("module")
            or ""
        ).strip()
        if theory:
            source_import_guidance = (
                f'SOURCE HARNESS THEORY IMPORT: imports "{theory}"\n'
                f"SOURCE HARNESS ITEM NAME: `{source_subject}`\n"
                "Use this exact session-qualified theory name in every source run.code; "
                "do not shorten it. The session-qualified theory import is not a namespace "
                "prefix for constants: invoke the judged item using the exact item name above, "
                "without prepending the session name. Write Isabelle symbols in accepted source syntax "
                "(`\\<lambda>`, `\\<Rightarrow>`, and so on), not Unicode glyphs such as `λ`.\n"
            )
    section_export_guidance = ""
    if prompt_version in {
        "semantic-alignment-v2",
        "semantic-alignment-v3",
        "semantic-alignment-v4",
        "semantic-alignment-v5",
        "semantic-alignment-v6",
        "semantic-alignment-v7",
        "semantic-alignment-v8",
        "semantic-alignment-v9",
        "semantic-alignment-v10",
        "semantic-alignment-v11",
        "semantic-alignment-v12",
        "semantic-alignment-v13",
        "semantic-alignment-v21",
        "semantic-alignment-v22",
        "semantic-alignment-v23",
        "semantic-alignment-v24",
        "semantic-alignment-v25",
        "semantic-alignment-v26",
        "semantic-alignment-v27",
    }:
        if source_language == "coq":
            section_export_guidance = """   Important Coq rule: `section_context` is ambient extraction metadata, not the exported
   binder list. Coq generalizes only Section variables on which the declaration actually
   depends. `Set Default Proof Using "Type"` and an explicit `Proof using` can exclude ambient
   variables that do not occur in the theorem type; merely being available to the proof script
   or calling a lemma from the same Section does not establish an exported binder. Never report
   a removed/added assumption merely because a variable was active in the Section. Establish
   exported arity from `Check`/`Print` when Coq is available, or from the declaration type and
   actual generalized dependencies. If that cannot be established, return `uncertain`; do not
   invent an extra source argument.
"""
        elif source_language == "isabelle":
            section_export_guidance = """   Important Isabelle rule: locale and context assumptions may be inherited rather than
   repeated textually in an item's statement. Inspect normalized `context`, locale inheritance,
   compiler-resolved dependencies, and interpretations before claiming an assumption was
   dropped. An indirect dependency is not a semantic weakening. If compiler context/type
   information is unavailable or a locale edge is unresolved, return `uncertain`; do not infer
weakening from surface syntax alone. Conversely, a definition-like command inside a locale does
   not automatically take every locale assumption as a public precondition. When
   `type_compiler_category` is `const` or `type`, use that compiler-selected entity's
   `type_signature` as the exported interface; do not copy premises from a generated `*_def`
   theorem merely because it is proved in the locale context. For an inductive or other
   declaration made inside a locale, inspect `compiler_rule_surface`: it contains the
   compiler-exported definition equation and immediate generated rule family, including each
   rule's dependency names. Inspect the constant, definition
   equation, introduction, elimination, and simplification rules together. A locale premise on
   generated convenience theorems is not automatically an input of the declared relation. For
   a declaration whose normalized `context` contains a compiler-validated locale, distinguish
   the raw constant telescope from the source item's semantic/client domain. If an assumption-free
   definition/fixed-point equation is externally accessible, the raw relation is part of the
   public source interface. If that equation is `external_name_not_accessible` and every public
   constructor/observer retains the locale premise, compare the item under the inherited locale
   domain; a proposed counterexample that deliberately violates that locale is
   `not_same_abstract_input`, not a semantic mismatch. The compiler-selected primary constant
   telescope remains authoritative for an ordinary public locale definition: a locale premise
   appearing only on a generated `*_def`, cases, or induction theorem is not by itself an input
   of that constant. Therefore, do not report `visibility_mismatch` merely because Lean exposes
   definitional reduction or a native eliminator more directly than those generated source
   theorems. Compare behavior on the inherited locale domain. A visibility mismatch requires
   the normalized source item itself to be explicitly `private`/hidden (or equivalent
   compiler-backed evidence that the primary item, not just a generated equation, is unavailable)
   while the paired target declaration is public. Establish that boundary with separate
   importing-client probes.
   Checking that the target raw declaration name is private is insufficient when a public definition unfolds to it.
   Require a behavioral difference in the relation or a compiler-backed proof about the
   source and target client-accessibility boundary. Presence in
   `Export_Theory` alone does not prove that a package-internal equation can be named by source
   clients: when the conclusion depends on such accessibility, run a minimal compiler-valid
   Isabelle theory using the supplied `external_name`; also run the relevant operation from a
   separate imported Lean client rather than from the defining file. If either probe is
   impractical, return `uncertain`, never `aligned` on an assumed visibility result. Conversely,
   if the constant/equation or every public observation genuinely retains the locale premise,
   preserve it. If accessibility cannot be established, return `uncertain`.
   An Isabelle `interpretation` is an aggregate source command. When
   `type_compiler_category` is `locale_interpretation_surface`, compare its locale name and
   instantiation equations with the target package plus companion declarations. Never replace
   the whole interpretation's interface with the first generated constant (for example
   `cbvs.freshA`); generated constants are members of the interpretation surface, not the
   interpretation itself.
"""
    compiler_surface_guidance = ""
    if prompt_version in {
        "semantic-alignment-v5",
        "semantic-alignment-v6",
        "semantic-alignment-v7",
        "semantic-alignment-v8",
        "semantic-alignment-v9",
        "semantic-alignment-v10",
        "semantic-alignment-v11",
        "semantic-alignment-v12",
        "semantic-alignment-v13",
        "semantic-alignment-v21",
        "semantic-alignment-v22",
        "semantic-alignment-v23",
        "semantic-alignment-v24",
        "semantic-alignment-v25",
        "semantic-alignment-v26",
        "semantic-alignment-v27",
    }:
        compiler_surface_guidance = """   The source payload may include `compiler_declared_surface`. These are prover-exported
   public constants/types generated by the outer declaration after known BNF/testing internals
   were removed. For datatypes, quotients, records, and similar declarations, explicitly check
   every semantically observable constructor, discriminator, selector, map, relator, and recursor
   that is present there and relevant to the source contract or downstream use. Companion Lean
   declarations in the same translated module may implement that surface even when the matched
   target span is only the primary type declaration. Do not return `aligned` merely from the
   primary type shape while ignoring a listed observable companion; cite its target evidence or
   return `uncertain`. In particular, an Isabelle generated `*_axioms` predicate is not preserved
   merely because its fields are projections of a larger Lean structure. When source code can
   construct or consume that axioms-only predicate independently of inherited locale assumptions,
   the target must expose an independently constructible API with exactly that assumption set (or
   a proved equivalence). A larger bundle with extra inherited fields is a stronger precondition,
   not a target-native replacement. The payload may also include `compiler_rule_surface`, whose
   `qualified_name` entries expose definition equations and immediate generated rules. Return one
   `compiler_surface_checks` entry first for every `compiler_declared_surface[].name`, then for every
   `compiler_rule_surface[].qualified_name`, preserving those two array orders, with an explicit
   disposition and concrete target evidence. Return an empty array only when neither compiler
   surface is supplied or the job is unmatched. When a rule has
   `external_name_compiler_validated=true`, its `source_visibility` is the result of a separate
   compiler-valid importing Isabelle session and is authoritative: `external_name_validated`
   means lookup succeeded, while `external_name_not_accessible` means lookup failed. Do not
   claim that Isabelle or an external probe is unavailable for such a rule, and do not rerun
   that already completed visibility check.
"""
    decision_protocol_guidance = ""
    alignment_direction_guidance = (
        "Do not accept target-domain extension as a mismatch merely because it exists; "
        "apply source-to-target preservation direction."
    )
    if prompt_version in {"semantic-alignment-v21", "semantic-alignment-v22"}:
        alignment_direction_guidance = """V21+ judges equivalence of the declared public
interface, not merely one-way refinement. A genuine public target-domain extension or changed
arity is therefore a mismatch when no explicit representation bridge restricts it back to the
source domain. Because no same-domain behavioral input exists in a target-only region, use a
compiler-validated interface witness for that case; never disguise a target-only inhabitant as
a bilateral behavioral counterexample. If the extra target representation is private, unreachable,
or quotiented away by the public bridge, it is not a semantic extension. When compiler interface
metadata is incomplete for a translated type, compare a public invariant as the bilateral
observation: prove that every source inhabitant satisfies it and prove that a target inhabitant
violates it. The shared abstract input is then the matched type/interface and the differing output
is the truth of that invariant; merely exhibiting a target-only raw value is still insufficient."""
        decision_protocol_guidance = """   V21+ contract-first decision procedure (complete this reasoning before writing any harness):
   a. Reconstruct the exported source contract and target contract from the compiler-selected
      types, declaration text, inherited context, and the bounded dependency/rule surfaces.
      Proof scripts establish truth but are not themselves translated behavior.
   b. Alpha-normalize binders and state an explicit representation relation for every differing
      source/target type. Compare semantic roles and dependency meaning, not identifier spelling,
      constructor spelling, reducibility, container layout, proof style, or intermediate list size.
   c. Check source-domain coverage, premises, conclusion, and each externally observable branch.
      A candidate mismatch is valid only in the shared abstract input domain and only when the
      compared outputs are observations of the judged declarations under the stated relation.
      Reject witnesses that compare different abstract inputs, target-only inhabitants, raw
      representations, helper behavior, proof terms, or unobservable intermediate artifacts.
   d. Attempt both hypotheses: first construct the strongest semantic bridge supporting alignment;
      then try to refute that exact bridge at boundary/base/constructor cases. A surface difference
      is not a refutation. Conversely, compilation and a few agreeing examples do not override a
      contract or branch difference.
   e. Commit to the semantic verdict before constructing evidence. Then build the smallest
      standalone native harness that demonstrates that decision. Do not change the verdict merely
      because one attempted harness is inconvenient; repair the harness or use another valid input.
      For alignment, choose three semantically distinct classes when available: a base/constructor
      case, a boundary or guard case, and a nontrivial recursive/composed case. Repeating the same
      branch with cosmetically different literals is weak evidence.
"""
    elif prompt_version in {
        "semantic-alignment-v23",
        "semantic-alignment-v24",
        "semantic-alignment-v25",
        "semantic-alignment-v26",
        "semantic-alignment-v27",
    }:
        alignment_direction_guidance = """V23 judges source-to-target semantic
preservation, not equality of the two public invocation domains. Establish a total bridge for
every valid source input and show that the related target observation preserves its result.
Additional target inputs, weaker target preconditions, erased proof fields, or a more general
target parameter are not mismatches by themselves. Never use a target-only inhabitant as a
counterexample or as a structural rejection. They matter only when the judged source item is
itself a type/record/interface and the extra target inhabitant is an observable output of that
declaration, or when it changes behavior on a source-related input. A source input with no target
representative remains `source_domain_loss` and may use a compiler-validated interface witness."""
        decision_protocol_guidance = """   V23 directional contract procedure (complete this reasoning before writing any harness):
   a. Reconstruct the compiler-exported source and target contracts. Define a total
      source-to-target input relation and an output observation relation independently of the
      candidate examples. Compare semantic roles, not spelling, proof fields, packaging, or
      intermediate representation layout.
   b. Test coverage direction explicitly: every valid source input must have a related target
      input. Ignore target-only inputs unless the judged declaration itself produces a type,
      record, constructor family, or interface whose inhabitants are the semantic output.
   c. Use canonical value preservation for corresponding scalar outputs (`Z`/`Int`,
      `nat`/`Nat`, and positive integers embedded in naturals). Do not invent an offset, sign
      change, permutation, or quotient after observing outputs merely because it makes the
      statements fit. A noncanonical output bridge needs independent evidence in the declared
      translation API or a constructor/observer isomorphism used consistently downstream.
   d. For a theorem whose conclusion contains executable functions, relations, projections, or
      indices, compare the denotations of corresponding observable subterms on the same abstract
      input. Two instantiated theorems being separately provable is not enough: self-consistent
      equalities can both be true while their corresponding computed values differ. Probe
      boundary, negative/signed, base-constructor, and nontrivial recursive cases as applicable.
   e. First build the strongest independently justified bridge, then try to refute that exact
      bridge. Commit to the semantic verdict before constructing harnesses. Repair harness syntax
      without changing the verdict unless compiler diagnostics disprove the semantic relation.
      For alignment, use three semantically distinct source-domain cases when available.
"""
        if prompt_version in {"semantic-alignment-v24", "semantic-alignment-v25", "semantic-alignment-v26", "semantic-alignment-v27"}:
            decision_protocol_guidance += """   f. A mismatch in a dependency or helper counts for the current theorem only when a
      concrete input satisfying every source premise reaches that differing behavior and changes
      an observable term in the current contract. Do not reject a theorem for a tie, error, or
      branch that its own premises make unreachable, or when the current conclusion is invariant
      under that dependency difference.
   g. Preserve the judged declaration's own source coverage. If a valid source invocation cannot
      invoke the target declaration because the target added a premise, return
      `source_domain_loss`; independently reproving the same conclusion through another target
      lemma does not restore the translated declaration's missing interface.
"""
    contract_edge_guidance = """5. An added target assumption or unrepresentable source input is a real loss of
   source coverage. A removed source assumption, totalized partial function, erased proof field,
   or broader target input type is not a mismatch by itself when all source-related behavior is
   preserved. An erased dependent result, omitted constructor/property, vacuous proposition, or
   changed observable output remains a mismatch when it loses information or changes behavior
   for a valid source input. For a judged type/record/interface declaration, its inhabitants and
   public constructors are outputs, so extra or missing target inhabitants require an explicit
   representation bridge.""" if prompt_version in {"semantic-alignment-v23", "semantic-alignment-v24", "semantic-alignment-v25", "semantic-alignment-v26", "semantic-alignment-v27"} else """5. An added assumption is a real loss of generality. A removed source assumption, erased
   dependent result, totalized partial/source-preconditioned function, vacuous proposition,
   or omitted constructor/property is also a real mismatch unless a proved bridge preserves
   the source contract."""
    v24_scope_override = """For V24, override decision-table item 3 above: coverage belongs to the
judged target declaration itself. If an added target premise excludes a valid source invocation,
record compiler-validated `source_domain_loss` even when some other target proof can establish the
same mathematical conclusion. Conversely, a dependency difference is behavioral evidence only on
an input satisfying all premises of the judged source item.""" if prompt_version == "semantic-alignment-v24" else (
        """For V25, the scope-witness exception above is disabled: `not_aligned` always requires
a two-sided compiler-verified counterexample with an output from each language. If the target
cannot be invoked on the proposed source input, or no such counterexample can be constructed,
return `uncertain` rather than `not_aligned`."""
        if prompt_version in {"semantic-alignment-v25", "semantic-alignment-v26", "semantic-alignment-v27"}
        else ""
    )
    matched_outcome_guidance = (
        """For V25 matched jobs, return `aligned` or `not_aligned` only with the required
executable evidence. Return `uncertain` when that evidence cannot be produced; `not_judged`
remains reserved for unmatched jobs."""
        if prompt_version in {"semantic-alignment-v25", "semantic-alignment-v26", "semantic-alignment-v27"}
        else """For matched jobs,
`uncertain` and `not_judged` are forbidden final answers. Return `aligned` or `not_aligned`
with the corresponding evidence; correction feedback will identify evidence that must be
repaired."""
    )
    coq_harness_syntax_guidance = (
        """   For Coq proof harnesses, use `Theorem name : claim. Proof. ... Qed.` (Coq does not accept
   Lean-style `Theorem name : claim := term`) and use explicit proof steps/imports instead of
   embedding bare `ltac:(...)` terms inside a theorem application.
"""
        if prompt_version in {"semantic-alignment-v26", "semantic-alignment-v27"}
        else ""
    )
    lean_named_argument_guidance = (
        """Lean named arguments in applications use parentheses such as `(α := Nat)`, never
braces such as `{α := Nat}` (which Lean parses as term/record notation).
"""
        if prompt_version in {"semantic-alignment-v26", "semantic-alignment-v27"}
        else ""
    )
    strict_gate_guidance = ""
    compiler_command_guidance = ""
    required_examples = aligned_example_requirement(prompt_version)
    example_count_text = "one" if required_examples == 1 else "three"
    example_noun = "example" if required_examples == 1 else "examples"
    entry_noun = "entry" if required_examples == 1 else "entries"
    object_noun = "object" if required_examples == 1 else "objects"
    distinct_text = (
        "a concrete source/target input pair"
        if required_examples == 1
        else "three distinct concrete source/target input pairs"
    )
    if prompt_version in {
        "semantic-alignment-v12",
        "semantic-alignment-v13",
        "semantic-alignment-v21",
        "semantic-alignment-v22",
        "semantic-alignment-v23",
        "semantic-alignment-v24",
        "semantic-alignment-v25",
        "semantic-alignment-v26",
        "semantic-alignment-v27",
    }:
        compiler_command_guidance = (
            "SOURCE COMPILER COMMAND: "
            + json.dumps(list(task.source.compiler_command), ensure_ascii=False)
            + "\n"
        )
        strict_gate_guidance = f"""
NON-NEGOTIABLE {prompt_version.upper()} OUTPUT GATE: `aligned` requires at least {example_count_text} complete
source/target {example_noun}; `not_aligned` requires at least one complete source/target
counterexample. If an attempted observation fails, repair it or choose another valid input;
only protocols that permit abstention may return `uncertain`.
The schema DOES provide both `examples` and `counterexamples`. Populate each observation
with exactly this shape (all shown fields are required):
{{
  "id": "distinct-id",
  "source": {{
    "subject": {json.dumps(source_subject, ensure_ascii=False)},
    "input": {{"description": "...", "expression": "literal input"}},
    "output": {{"description": "...", "expression": "exact full run.claim"}},
    "run": {{
      "language": "{source_language}", "mode": "prove",
      "entrypoint": "named harness theorem", "invocation": "judged item applied to input",
      "claim": "input/output proposition", "code": "complete standalone program",
      "expected_stdout": null
    }}
  }},
  "target": {{
    "subject": {json.dumps(target_subject, ensure_ascii=False)},
    "input": {{"description": "...", "expression": "literal input"}},
    "output": {{"description": "...", "expression": "exact full run.claim"}},
    "run": {{
      "language": "lean", "mode": "prove",
      "entrypoint": "named harness theorem", "invocation": "judged item applied to input",
      "claim": "input/output proposition", "code": "complete standalone program",
      "expected_stdout": null
    }}
  }},
  "input_alignment": {{"status": "same", "reason": "..."}},
  "output_alignment": {{"status": "same", "reason": "..."}}
}}
The two `subject` strings above are literal required values copied from the normalized
compiler indexes. Do not put a stable item ID such as `file:name:offset` in `subject`.
For a theorem example, `invocation` is the original judged theorem applied to concrete
binders and premise proofs; `claim`/`output.expression` is its instantiated conclusion, and
the named harness theorem uses that invocation. The native verifier rechecks `invocation`
after the named harness declaration. Every auxiliary premise named by the invocation must
therefore be a top-level declaration still in scope at that point, and must be namespace-
qualified in Lean when necessary; never refer to a theorem-local `have`, `let`, or proof
block fact. Put at least {example_count_text} such {object_noun} in `examples`.
"""
    return f"""You are a read-only semantic-alignment judge for a {source_language}-to-Lean formal-code translation benchmark.

SOURCE CODEBASE DIRECTORY: {task.source.root}
TRANSLATED LEAN CODEBASE DIRECTORY: {task.target.project}
{compiler_command_guidance}\
{source_import_guidance}\
{strict_gate_guidance}{lean_named_argument_guidance}

You may inspect both directories and their dependency declarations in detail. Do not edit
anything. Judge source meaning against target meaning, not proof style, identifier spelling,
or whether both files merely compile.

For a matched item:
1. Confirm that these are genuinely corresponding semantic items. If not, return
   match_status=wrong_match and, if you locate it, suggested_target. Use
   alignment=not_judged when only the pairing is wrong; use alignment=not_aligned only
   when you also supply the concrete source/paired-target counterexample required below.
2. Compare every binder, Section variable/hypothesis, quantifier, domain, codomain,
   precondition, postcondition, dependent refinement, constructor, recurrence, and observable
   behavior. Library/representation changes are acceptable only with a valid equivalence or
   refinement bridge.
{section_export_guidance}\
{compiler_surface_guidance}\
{decision_protocol_guidance}\
3. Return alignment=aligned only with at least {example_count_text} {entry_noun} in `examples` using
   {distinct_text}, and no
   entries in `counterexamples`. Every example must contain a source-language observation and
   a Lean observation. Each side must name the actual judged declaration, give a concrete input
   expression and output expression, and provide a complete standalone run. Set
   `run.invocation` to the exact expression that applies the judged declaration to that input;
   it must occur in executable `run.code`. Set `input.expression` to the complete literal
   argument tail after the judged subject, including type/proof arguments—not one selected token
   buried in a larger call. For a nullary value, use the complete invocation as
   `input.expression`. For a nullary type declaration, the input(s) may instead be concrete
   inhabitants explicitly ascribed to that judged type. Pass each complete typed
   inhabitant as the final argument of a semantic observer (for example arithmetic, comparison,
   elimination, or an identity observer); do not inspect compiler metadata or representation
   layout. Do not hide the input behind a local definition, abbreviation, or variable. The claim
   must bind that invocation to the output.
   Use `mode=prove` when the prover kernel checks a proposition or an
   input/output equality; use `mode=evaluate` only when the command emits a stable textual value
   and set `expected_stdout` to that value. The harness executes every run. Executed examples
   are supporting evidence, not a proof of universal equivalence.
4. Return alignment=not_aligned only with at least one entry in `counterexamples` and no
   entries in `examples`. Each counterexample must satisfy the same two-sided execution rules,
   claim `input_alignment.status=same`, and claim `output_alignment.status=different`. A
   compiler-backed `interface_witness` may support the explanation but never replaces the
   required executable counterexample. If no two-sided executable/provable counterexample can
   be supplied, return alignment=uncertain rather than not_aligned.
   A source-polymorphic binder restricted to one concrete target type remains an interface
   warning, but it must be demonstrated by a two-sided concrete instantiation counterexample
   before assigning not_aligned.
   For a theorem or noncomputable item, an output may be a kernel-checked proposition
   observation (`mode=prove`) rather than a runtime value. The source and target runs must each
   prove the claimed observation for their concrete input. A target-only value, a bare type
   error, a candidate output not connected to the judged operation, or a proof about a helper
   instead of the judged declaration is not a counterexample.
   The `run.claim` is the authoritative input-to-output proposition. For a function/value
   observation, put the exact `run.invocation` in `run.claim` (normally an equality to
   `output.expression`). For a theorem observation, `run.invocation` may instead be the proof/fact
   application supplying `run.claim`; the harness directly type-checks that application against
   the claim. Put the actual item name, `input.expression`, `run.invocation`, and
   `output.expression` in executable code rather than comments. For
   `mode=prove`, define a named theorem in `run.code`, put its exact qualified name in
   `run.entrypoint`, set `expected_stdout` to null, and give its exact proposition (without an
   Isabelle outer quote) in `run.claim`. Set `output.expression` to that entire proposition,
   exactly—not merely the right-hand-side value or a token appearing inside it. The harness adds
   a second type-check tying that theorem to the exact output claim. For
   `mode=evaluate`, put the exact evaluated `run.invocation` in `run.claim`, set `expected_stdout`
   exactly equal to `output.expression`; `entrypoint` must be null. For Coq and Lean, the
   pipeline itself appends and
   delimits a fresh evaluation of the exact invocation, so unrelated output from model code
   cannot satisfy this check, and the normalized delimited output must exactly equal
   `expected_stdout`. For Isabelle, whose batch build omits `value` messages, it appends
   and kernel-checks the exact equality `invocation = output.expression` using `by eval`.
   Do not use raw expected compiler failure as evidence; express negative observations
   with a passing language-native assertion.
   Every `run.code` must be standalone in the configured repository environment. Inspect the
   original source file and reproduce every direct import needed by names in the harness; in
   particular, importing a Coq source module does not necessarily re-export short names from
   that module's own dependencies.
{coq_harness_syntax_guidance}   The only non-mechanical parts are whether the two language-specific inputs denote the same
   abstract input, whether their outputs denote the same abstract output, and the final aligned
   generalization beyond the examples. The complete within-language input-to-output chain must
   be executable and verified by the harness.
   Do not use embedded ML, setup/oracle hooks, user axioms/parameters, `sorry`, `admit`,
   Lean `native_decide`, or other trust escapes in an observation harness;
   prover-specific policy rejects them. Use kernel-checked `decide` for closed Lean facts.
{contract_edge_guidance}

For source_unmatched, search the translated directory for a missed correspondence. Use
match_status=source_unmatched and failure category missing_target_item only if none exists.
For target_unmatched, classify the target
as a helper/bridge, proof of a matched spec, duplicate, unrelated addition, or uncertain.
Unmatched-only jobs use alignment=not_judged.

Evidence locations must point into the two supplied directories. Do not claim a run was
verified merely because you executed it while reasoning: the harness independently reruns and
gates every returned source/target observation. Unmatched-only jobs must return empty
`examples` and `counterexamples` arrays.

For v14-v16 and v20+ matched jobs, inspect `counterexample_search_scope` before choosing
observations. V20 obtains source branches from Rocq kernel reduction and target branches from
Lean equation-compiler theorems over a bounded relevant dependency slice. Compare the native
source and target branch statements, infer candidate path regions, and exercise the supplied
`boundary_candidates` immediately below, at, and above numeric boundaries.
These hints are not evidence and may be incomplete; accept a mismatch only after the normal
two-sided compiler counterexample (or permitted source-domain-loss witness) succeeds.

V19+ provides `compiler_interface_analysis`, `compiler_warnings`, and `domain_partition` for
both source and target as heuristic feedback only. They never determine the verdict, regardless
of a warning's severity or a side's `compiler_validated` value. Independently inspect the
declarations, decide whether each warning is real, and explain any accepted or rejected bridge.
This V19 rule overrides item 4 above: a final `not_aligned` verdict may use either (a) a verified
two-sided semantic counterexample, or (b) a scope-comparison basis establishing that the target
scope is strictly smaller than the source scope. Compiler/interface information may support
basis (b), but only after you independently accept the scope relation; it remains heuristic and
never selects the verdict itself. For basis (b),
return empty examples/counterexamples and a complete `interface_witness` with status=`found`,
the source and target interfaces, a precise explanation of why no valid bridge preserves the
required contract, source and target evidence, and the `source_domain_loss` category. The
   `interface_witness.compiler_validated` field reports provenance; V21+ requires it for a structural
rejection outside the shared behavioral domain. Use this decision table for a source input such
as `u = 0` that a target wrapper excludes:
1. If the target input type or operation cannot represent the source input, return
   `not_aligned` with a genuine `source_domain_loss` scope witness.
2. If the target operation accepts the input but produces a different output or proposition,
   return `not_aligned` with a behavioral counterexample.
3. If the wrapper excludes the input but target definitions independently prove the source
   property there, return `aligned` and explain that the proof-interface restriction is
   semantically redundant.
4. If neither the source property nor its failure can be proved for the excluded input, return
   `not_aligned` with a `source_domain_loss` scope witness: the judged target declaration has not
   preserved the source declaration's coverage.
{v24_scope_override}
For V21-v22 only, basis (b) also covers a compiler-validated inequality in the opposite direction
under the bidirectional public-interface policy above. Use the precise matching interface kind
and category (for example `target_domain_extension`); this exception is unavailable when either
interface is merely guessed from text.
{alignment_direction_guidance} A general representation/interface warning that does not prove
public-interface inequality needs a behavioral counterexample; otherwise return `aligned` with
the required compiler-verified examples and an explanation of the accepted bridge. {matched_outcome_guidance}
Search behavioral counterexamples in `domain_partition.behavioral_counterexample_search_region`.
Instantiate `typed_witness_plan` templates rather than inventing binder order; the pipeline
normalizes the auxiliary input expression from the invocation and then trusts only native
elaboration and compiler replay.

Return only the JSON object required by the output schema. The IDs must be copied exactly
from this job payload.

JOB PAYLOAD:
{json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=prompt_version == "semantic-alignment-v27")}
"""


def archive_incompatible_judge_state(
    task: TaskConfig,
    workspace: Path,
    source_index: dict[str, Any],
    target_index: dict[str, Any],
    new_plan: dict[str, Any],
    *,
    old_plan: dict[str, Any] | None,
    old_target_index: dict[str, Any] | None,
) -> dict[str, Any]:
    """Archive cached jobs that cannot be replayed under a replacement plan.

    Judge keys intentionally omit prompt and matcher metadata. A forced replan
    can therefore leave an orphaned result key, or retain a key whose prompt
    changed. Both cases must leave the active result directory before report
    aggregation. Prompt-compatible results remain active so a small matcher
    correction does not cause an expensive repository-wide LLM rerun.
    """

    if old_plan is None:
        return {
            "archived": False,
            "reason": "no_previous_plan",
            "archived_job_files": 0,
            "archived_result_files": 0,
            "archived_report_files": 0,
        }
    old_plan_sha256 = sha256_json(old_plan)
    new_plan_sha256 = sha256_json(new_plan)
    if old_plan_sha256 == new_plan_sha256:
        return {
            "archived": False,
            "reason": "plan_unchanged",
            "archived_job_files": 0,
            "archived_result_files": 0,
            "archived_report_files": 0,
        }

    prompt_version = new_plan.get("prompt_version", "semantic-alignment-v1")
    source_by_id = {
        item["id"]: item for item in source_index.get("declarations", [])
    }
    target_by_id = {
        item["id"]: item for item in target_index.get("declarations", [])
    }
    attach_relational_dependency_context(source_by_id, target_by_id)
    # Plans are persisted with sorted JSON keys before judge-run reloads them.
    # Reproduce that representation here, otherwise harmless dictionary
    # insertion order differences would invalidate every cached prompt.
    normalized_new_plan = json.loads(
        json.dumps(new_plan, ensure_ascii=False, sort_keys=True)
    )
    expected_prompt_hashes = {
        job["key"]: sha256_bytes(
            render_judge_prompt(
                task,
                job,
                source_by_id.get(job.get("source_id")),
                target_by_id.get(job.get("target_id")),
                prompt_version=prompt_version,
            ).encode("utf-8")
        )
        for job in normalized_new_plan["jobs"]
    }

    judge_directory = workspace / JUDGE_DIRECTORY
    incompatible: dict[str, list[Path]] = {"jobs": [], "results": []}
    for kind in ("jobs", "results"):
        directory = judge_directory / kind
        if not directory.is_dir():
            continue
        for path in sorted(directory.glob("*.json")):
            expected_hash = expected_prompt_hashes.get(path.stem)
            try:
                actual_hash = read_json(path).get("prompt_sha256")
            except PipelineError:
                actual_hash = None
            if expected_hash is None or actual_hash != expected_hash:
                incompatible[kind].append(path)

    archive_parent = judge_directory / "archive"
    archive_parent.mkdir(parents=True, exist_ok=True)
    base_name = old_plan_sha256[:16]
    archive_directory = archive_parent / base_name
    suffix = 2
    while archive_directory.exists():
        archive_directory = archive_parent / f"{base_name}-{suffix:03d}"
        suffix += 1
    archive_directory.mkdir()

    artifacts_directory = archive_directory / "artifacts"
    artifacts_directory.mkdir()
    write_json(artifacts_directory / JUDGE_PLAN, old_plan)
    if old_target_index is not None:
        write_json(artifacts_directory / TARGET_INDEX, old_target_index)
    archived_report_files: list[str] = []
    active_artifacts_directory = workspace / "artifacts"
    for report_name in (JUDGE_REPORT_JSON, JUDGE_REPORT_MD):
        report_path = active_artifacts_directory / report_name
        if not report_path.is_file():
            continue
        destination = artifacts_directory / report_name
        report_path.rename(destination)
        archived_report_files.append(
            str(destination.relative_to(workspace))
        )

    archived_paths: dict[str, list[str]] = {"jobs": [], "results": []}
    for kind, paths in incompatible.items():
        if not paths:
            continue
        destination_directory = archive_directory / kind
        destination_directory.mkdir()
        for path in paths:
            destination = destination_directory / path.name
            path.rename(destination)
            archived_paths[kind].append(
                str(destination.relative_to(workspace))
            )

    manifest = {
        "version": 1,
        "old_plan_sha256": old_plan_sha256,
        "new_plan_sha256": new_plan_sha256,
        "old_prompt_version": old_plan.get(
            "prompt_version", "semantic-alignment-v1"
        ),
        "new_prompt_version": prompt_version,
        "archived_job_files": len(archived_paths["jobs"]),
        "archived_result_files": len(archived_paths["results"]),
        "archived_report_files": len(archived_report_files),
        "preserved_compatible_job_files": len(
            list((judge_directory / "jobs").glob("*.json"))
        ),
        "preserved_compatible_result_files": len(
            list((judge_directory / "results").glob("*.json"))
        ),
        "paths": {
            **archived_paths,
            "reports": archived_report_files,
        },
    }
    write_json(archive_directory / "manifest.json", manifest)
    return {
        "archived": True,
        "reason": "plan_changed",
        "archive_directory": str(archive_directory),
        **manifest,
    }


def _item_name_from_id(item_id: str | None) -> str | None:
    if not item_id:
        return None
    parts = item_id.rsplit(":", 2)
    return parts[-2] if len(parts) >= 2 else None


def _references_subject(text: str, subject: str) -> bool:
    if re.search(
        rf"(?<![A-Za-z0-9_.'])(?:_root_\.)?{re.escape(subject)}"
        r"(?![A-Za-z0-9_'])",
        text,
    ):
        return True
    basename = subject.rsplit(".", 1)[-1]
    prefix_chars = "A-Za-z0-9_." if "." in subject else "A-Za-z0-9_"
    return bool(
        re.search(
            rf"(?<![{prefix_chars}']){re.escape(basename)}(?![A-Za-z0-9_'])",
            text,
        )
    )


def _strip_complete_outer_parentheses(expression: str) -> str:
    expression = normalize_space(expression).strip()
    while expression.startswith("(") and expression.endswith(")"):
        depth = 0
        for index, char in enumerate(expression):
            depth += char == "("
            depth -= char == ")"
            if depth == 0:
                if index != len(expression) - 1:
                    return expression
                expression = expression[1:-1].strip()
                break
            if depth < 0:
                return expression
        else:
            return expression
    return expression


def _invocation_binds_complete_input(
    invocation: str,
    subject: str,
    input_expression: str,
) -> bool:
    """Require the input to be the whole application tail, not a buried token.

    A judged instance/implementation value can be passed to a generic observer
    rather than occur at the head of the application (for example,
    ``@show _ judgedShow (value)``).  In that case accept only a complete,
    explicitly parenthesized final input.  Keeping this case terminal and
    parenthesized prevents a selected argument of an ordinary multi-argument
    subject application from passing as the whole input.
    """
    normalized_invocation = _strip_complete_outer_parentheses(invocation)
    literal_input = normalize_space(input_expression).strip()
    # Models and hand-written harnesses commonly parenthesize a complete Coq
    # theorem application, for example ``(lemma arg proof)``.  The outer pair
    # is not part of the argument tail and must not make an otherwise exact
    # subject/input binding fail.  Only peel a pair that encloses the entire
    # expression; parentheses belonging to arguments remain untouched.
    normalized_input = _strip_complete_outer_parentheses(input_expression)
    if normalized_invocation == normalized_input:
        return True
    candidates = sorted(
        {subject, subject.rsplit(".", 1)[-1]}, key=len, reverse=True
    )
    subject_occurs_at_head = False
    for candidate in candidates:
        if (
            literal_input.startswith("(")
            and literal_input.endswith(")")
            and re.search(
                rf":\s*{re.escape(candidate)}\s*\)$", literal_input
            )
            and normalized_invocation.startswith(literal_input)
            and re.fullmatch(
                r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*",
                normalized_invocation[len(literal_input) :].strip(),
            )
        ):
            return True
        pattern = re.compile(
            rf"(?<![A-Za-z0-9_']){re.escape(candidate)}(?![A-Za-z0-9_'])"
        )
        for match in pattern.finditer(normalized_invocation):
            prefix = normalized_invocation[: match.start()].strip()
            suffix = normalized_invocation[match.end() :].strip()
            qualified_alias_prefix = bool(
                re.fullmatch(
                    r"[@(\s]*(?:[A-Za-z_][A-Za-z0-9_']*\.)+",
                    prefix,
                )
            )
            if prefix.strip("(@ ") and not qualified_alias_prefix:
                if re.search(r":\s*$", prefix) and suffix.startswith(
                    normalized_input
                ):
                    remainder = suffix[len(normalized_input) :].strip()
                    if re.fullmatch(
                        r"\)+(?:\.[A-Za-z_][A-Za-z0-9_']*)*", remainder
                    ):
                        return True
                if (
                    not subject_occurs_at_head
                    and (
                        normalized_invocation.endswith(f"({normalized_input})")
                        # A concrete inhabitant of a nullary judged type normally
                        # needs its own type ascription, so the complete input is
                        # already parenthesized: `observe (0 : JudgedType)`.
                        or (
                            normalized_input.startswith("(")
                            and normalized_input.endswith(")")
                            and normalized_invocation.endswith(normalized_input)
                        )
                    )
                ):
                    return True
                continue
            subject_occurs_at_head = True
            if _strip_complete_outer_parentheses(suffix) == normalized_input:
                return True
    return False


def _declares_subject(language: str, code: str, subject: str) -> bool:
    basename = re.escape(subject.rsplit(".", 1)[-1])
    if language == "coq":
        introducers = (
            r"(?:Local\s+|Global\s+)?(?:Definition|Fixpoint|CoFixpoint|"
            r"Inductive|Variant|Record|Class|Instance|Axiom|Parameter|"
            r"Variable|Hypothesis|Let|Notation)"
        )
    elif language == "lean":
        introducers = (
            r"(?:private\s+|protected\s+|noncomputable\s+)?(?:def|abbrev|"
            r"theorem|lemma|axiom|opaque|inductive|structure|class|instance)"
        )
    else:
        introducers = (
            r"(?:definition|abbreviation|lemma|theorem|axiomatization|"
            r"consts|locale|inductive|inductive_set)"
        )
    return bool(
        re.search(
            rf"(?mi)^\s*{introducers}\s+{basename}(?![A-Za-z0-9_'])",
            code,
        )
    )


def _observation_static_errors(
    job: dict[str, Any],
    observation: dict[str, Any],
    *,
    kind: str,
) -> list[str]:
    errors: list[str] = []
    observation_id = observation.get("id")
    if not isinstance(observation_id, str) or not observation_id.strip():
        return [f"{kind} observation needs a nonempty id"]
    expected_names = {
        "source": _item_name_from_id(job.get("source_id")),
        "target": _item_name_from_id(job.get("target_id")),
    }
    expected_languages = {
        "source": job.get("source_language"),
        "target": "lean",
    }
    for side_name in ("source", "target"):
        prefix = f"{kind} {observation_id} {side_name}"
        side = observation.get(side_name)
        if not isinstance(side, dict):
            errors.append(f"{prefix} observation is absent")
            continue
        subject = side.get("subject")
        expected_name = expected_names[side_name]
        if (
            expected_name
            and isinstance(subject, str)
            and subject.rsplit(".", 1)[-1] != expected_name
        ):
            errors.append(
                f"{prefix} subject must name the judged declaration {expected_name}; "
                "use its compiler-indexed qualified/name spelling, not the stable "
                "file:name:offset item id"
            )
        run = side.get("run")
        if not isinstance(run, dict):
            errors.append(f"{prefix} run is absent")
            continue
        expected_language = expected_languages[side_name]
        if expected_language and run.get("language") != expected_language:
            errors.append(
                f"{prefix} run language must be {expected_language}"
            )
        mode = run.get("mode")
        if mode == "prove":
            if not run.get("entrypoint"):
                errors.append(f"{prefix} prove run needs an entrypoint")
            if run.get("expected_stdout") is not None:
                errors.append(
                    f"{prefix} prove run must have null expected_stdout"
                )
        elif mode == "evaluate":
            if run.get("entrypoint") is not None:
                errors.append(f"{prefix} evaluate run must not have an entrypoint")
            if not run.get("expected_stdout"):
                errors.append(
                    f"{prefix} evaluate run needs nonempty expected_stdout"
                )
            output_expression = (side.get("output") or {}).get("expression")
            if str(run.get("expected_stdout")) != str(output_expression):
                errors.append(
                    f"{prefix} expected_stdout must equal output.expression"
                )
        else:
            errors.append(f"{prefix} has unsupported run mode")
        claim = run.get("claim")
        invocation = run.get("invocation")
        input_expression = (side.get("input") or {}).get("expression")
        output_expression = (side.get("output") or {}).get("expression")
        if not isinstance(invocation, str) or not invocation.strip():
            errors.append(f"{prefix} run needs an invocation")
        else:
            if isinstance(subject, str) and not _references_subject(
                invocation, subject
            ):
                errors.append(f"{prefix} invocation does not call its subject")
            if (
                isinstance(subject, str)
                and isinstance(input_expression, str)
                and not _invocation_binds_complete_input(
                    invocation, subject, input_expression
                )
            ):
                errors.append(
                    f"{prefix} input.expression must be the complete argument "
                    "tail applied to the judged subject, the complete invocation "
                    "for a nullary value, or a complete terminal inhabitant "
                    "explicitly typed by a nullary judged type"
                )
        if not isinstance(claim, str) or not claim.strip():
            errors.append(f"{prefix} run needs a claim")
        elif mode == "prove":
            if (
                isinstance(output_expression, str)
                and normalize_space(output_expression) != normalize_space(claim)
            ):
                errors.append(
                    f"{prefix} prove output.expression must exactly equal run.claim"
                )
        elif mode == "evaluate" and isinstance(invocation, str):
            if normalize_space(claim) != normalize_space(invocation):
                errors.append(
                    f"{prefix} evaluate claim must equal invocation"
                )
    return errors


def normalize_typed_witness_bindings(verdict: dict[str, Any]) -> None:
    """Derive auxiliary input tails from invocations before native replay."""
    for collection in ("examples", "counterexamples"):
        for observation in verdict.get(collection, []):
            if not isinstance(observation, dict):
                continue
            for side_name in ("source", "target"):
                side = observation.get(side_name)
                if not isinstance(side, dict):
                    continue
                subject = side.get("subject")
                invocation = (side.get("run") or {}).get("invocation")
                input_value = side.get("input")
                if not (
                    isinstance(subject, str)
                    and isinstance(invocation, str)
                    and isinstance(input_value, dict)
                ):
                    continue
                current = input_value.get("expression")
                if isinstance(current, str) and _invocation_binds_complete_input(
                    invocation, subject, current
                ):
                    continue
                replacement = None
                for spelling in (subject, subject.rsplit(".", 1)[-1]):
                    matches = list(
                        re.finditer(
                            rf"(?<![A-Za-z0-9_']){re.escape(spelling)}(?![A-Za-z0-9_'])",
                            invocation,
                        )
                    )
                    if not matches:
                        continue
                    tail = invocation[matches[-1].end() :].strip()
                    candidates = [tail] if tail else [invocation]
                    if tail.endswith(")") and invocation.strip().startswith("("):
                        candidates.append(tail[:-1].rstrip())
                    replacement = next(
                        (
                            candidate
                            for candidate in candidates
                            if candidate
                            and _invocation_binds_complete_input(
                                invocation, subject, candidate
                            )
                        ),
                        None,
                    )
                    if replacement is not None:
                        break
                if replacement is not None:
                    input_value["expression"] = replacement


def validate_verdict(
    job: dict[str, Any],
    verdict: dict[str, Any],
    *,
    prompt_version: str = PROMPT_VERSION,
) -> list[str]:
    errors: list[str] = []
    if verdict.get("source_id") != job.get("source_id"):
        errors.append("source_id does not match job")
    if verdict.get("target_id") != job.get("target_id"):
        errors.append("target_id does not match job")
    match_status = verdict.get("match_status")
    alignment = verdict.get("alignment")
    if job["kind"] == "matched":
        if match_status not in {"confirmed", "wrong_match", "uncertain"}:
            errors.append("matched job has invalid match_status")
        if match_status == "confirmed" and alignment == "not_judged":
            errors.append("confirmed match must be semantically judged")
        if (
            prompt_version in {
                "semantic-alignment-v19",
                "semantic-alignment-v20",
                "semantic-alignment-v21",
                "semantic-alignment-v22",
                "semantic-alignment-v23",
                "semantic-alignment-v24",
            }
            and alignment not in {"aligned", "not_aligned"}
        ):
            errors.append(
                "v19+ matched jobs require a definitive aligned or not_aligned verdict"
            )
        if match_status == "wrong_match" and alignment not in {
            "not_judged",
            "not_aligned",
        }:
            errors.append(
                "wrong match must use alignment=not_judged or not_aligned"
            )
    elif job["kind"] == "source_unmatched":
        if match_status not in {"source_unmatched", "wrong_match", "uncertain"}:
            errors.append("source-unmatched job has invalid match_status")
        if alignment != "not_judged":
            errors.append("source-unmatched job must use alignment=not_judged")
        if (
            match_status == "source_unmatched"
            and "missing_target_item" not in verdict.get("failure_categories", [])
        ):
            errors.append(
                "confirmed source-unmatched job needs missing_target_item"
            )
    elif job["kind"] == "target_unmatched":
        if match_status not in {"target_unmatched", "uncertain"}:
            errors.append("target-unmatched job has invalid match_status")
        if alignment != "not_judged":
            errors.append("target-unmatched job must use alignment=not_judged")
        if verdict.get("target_disposition") is None:
            errors.append("target-unmatched job needs target_disposition")
    interface_witness = verdict.get("interface_witness")
    valid_interface_witness = False
    if not isinstance(interface_witness, dict):
        errors.append("interface_witness must be an object")
    elif interface_witness.get("status") == "found":
        interface_evidence = verdict.get("evidence", [])
        has_source_evidence = any(
            isinstance(item, dict) and item.get("side") == "source"
            for item in interface_evidence
        )
        has_target_evidence = any(
            isinstance(item, dict) and item.get("side") == "target"
            for item in interface_evidence
        )
        category_for_kind = {
            "domain_mismatch": "domain_mismatch",
            "codomain_mismatch": "codomain_mismatch",
            "arity_mismatch": "quantifier_or_binder_mismatch",
            "binder_mismatch": "quantifier_or_binder_mismatch",
            "visibility_mismatch": "visibility_mismatch",
            "source_domain_loss": "source_domain_loss",
            "target_domain_extension": "target_domain_extension",
            "interface_relation_failure": "interface_relation_failure",
        }.get(interface_witness.get("kind"))
        valid_interface_witness = (
            category_for_kind is not None
            and category_for_kind in verdict.get("failure_categories", [])
            and bool(interface_witness.get("source_interface"))
            and bool(interface_witness.get("target_interface"))
            and bool(interface_witness.get("explanation"))
            and (
                prompt_version in {
                    "semantic-alignment-v17",
                    "semantic-alignment-v18",
                    "semantic-alignment-v19",
                    "semantic-alignment-v20",
                    "semantic-alignment-v21",
                    "semantic-alignment-v22",
                    "semantic-alignment-v23",
                    "semantic-alignment-v24",
                    "semantic-alignment-v25",
                    "semantic-alignment-v26",
                    "semantic-alignment-v27",
                }
                or interface_witness.get("compiler_validated") is True
            )
            and has_source_evidence
            and has_target_evidence
        )
        if not valid_interface_witness:
            errors.append(
                "interface witness requires source/target interfaces, source/target "
                "evidence, a matching failure category, and compiler validation before v17"
            )
    examples = verdict.get("examples")
    counterexamples = verdict.get("counterexamples")
    if not isinstance(examples, list):
        errors.append("examples must be an array")
        examples = []
    if not isinstance(counterexamples, list):
        errors.append("counterexamples must be an array")
        counterexamples = []
    if alignment == "aligned":
        if match_status != "confirmed":
            errors.append("aligned verdict requires a confirmed match")
        required_examples = aligned_example_requirement(prompt_version)
        if len(examples) < required_examples:
            count_text = "one" if required_examples == 1 else "three"
            errors.append(
                f"aligned verdict requires at least {count_text} example"
                + ("s" if required_examples != 1 else "")
            )
        if counterexamples:
            errors.append("aligned verdict cannot contain counterexamples")
    elif alignment == "not_aligned":
        structural_rejection = valid_interface_witness and (
            (
                prompt_version in {"semantic-alignment-v21", "semantic-alignment-v22"}
                and interface_witness.get("compiler_validated") is True
                and interface_witness.get("kind")
                in {
                    "domain_mismatch",
                    "codomain_mismatch",
                    "arity_mismatch",
                    "binder_mismatch",
                    "source_domain_loss",
                    "target_domain_extension",
                    "interface_relation_failure",
                    "visibility_mismatch",
                }
            )
            or (
                prompt_version in {
                    "semantic-alignment-v16",
                    "semantic-alignment-v17",
                }
                and bool(
                    {
                        "source_domain_loss",
                        "target_domain_extension",
                        "interface_relation_failure",
                    }
                    & set(verdict.get("failure_categories", []))
                )
            )
            or (
                prompt_version in {
                    "semantic-alignment-v18",
                    "semantic-alignment-v19",
                    "semantic-alignment-v20",
                    "semantic-alignment-v21",
                    "semantic-alignment-v22",
                    "semantic-alignment-v23",
                    "semantic-alignment-v24",
                }
                and interface_witness.get("kind") == "source_domain_loss"
                and "source_domain_loss" in verdict.get("failure_categories", [])
            )
        )
        if not counterexamples and not structural_rejection:
            errors.append(
                "not_aligned verdict requires at least one two-sided counterexample"
            )
        if examples:
            errors.append("not_aligned verdict cannot contain aligned examples")
    elif alignment in {"uncertain", "not_judged"}:
        if alignment == "not_judged" and (examples or counterexamples):
            errors.append("not_judged verdict cannot contain observations")
        if alignment == "uncertain":
            abstention_text = " ".join(
                [
                    *(
                        str(value)
                        for value in verdict.get("differences", [])
                    ),
                    str(
                        (verdict.get("interface_witness") or {}).get(
                            "explanation", ""
                        )
                    ),
                ]
            ).lower()
            if "schema" in abstention_text and any(
                marker in abstention_text
                for marker in (
                    "example",
                    "counterexample",
                    "observation",
                    "evidence",
                    "harness",
                )
            ):
                errors.append(
                    "uncertain verdict falsely claims the active schema lacks an "
                    "examples/counterexamples field"
                )

    all_observations = [("example", item) for item in examples]
    all_observations.extend(
        ("counterexample", item) for item in counterexamples
    )
    ids = [
        item.get("id")
        for _, item in all_observations
        if isinstance(item, dict)
    ]
    if len(ids) != len(set(ids)):
        errors.append("observation ids must be unique within a verdict")
    example_input_pairs: set[tuple[str, str]] = set()
    for kind, observation in all_observations:
        if not isinstance(observation, dict):
            errors.append(f"{kind} observation must be an object")
            continue
        errors.extend(_observation_static_errors(job, observation, kind=kind))
        input_status = (observation.get("input_alignment") or {}).get("status")
        output_status = (observation.get("output_alignment") or {}).get("status")
        if kind == "example":
            if input_status != "same" or output_status != "same":
                errors.append(
                    f"example {observation.get('id')} must claim same input and output"
                )
            source_input = (
                (observation.get("source") or {}).get("input") or {}
            ).get("expression")
            target_input = (
                (observation.get("target") or {}).get("input") or {}
            ).get("expression")
            input_pair = (
                normalize_space(str(source_input)),
                normalize_space(str(target_input)),
            )
            if input_pair in example_input_pairs:
                errors.append(
                    "aligned examples must use distinct concrete source/target "
                    "input pairs"
                )
            example_input_pairs.add(input_pair)
        else:
            if input_status != "same" or output_status != "different":
                errors.append(
                    f"counterexample {observation.get('id')} must claim same input "
                    "and different output"
                )
    categories = verdict.get("failure_categories")
    if not isinstance(categories, list) or any(
        category not in FAILURE_CATEGORIES for category in categories
    ):
        errors.append("failure_categories contains unsupported values")
    confidence = verdict.get("confidence")
    if not isinstance(confidence, (int, float)) or not 0 <= confidence <= 1:
        errors.append("confidence must be between 0 and 1")
    if not isinstance(verdict.get("compiler_surface_checks"), list):
        errors.append("compiler_surface_checks must be an array")
    return errors


def _validate_compiler_surface_coverage(
    source_item: dict[str, Any] | None,
    verdict: dict[str, Any],
) -> list[str]:
    expected = [item["name"] for item in _compiler_declared_surface(source_item)]
    expected.extend(
        item["qualified_name"] for item in _compiler_rule_surface(source_item)
    )
    checks = verdict.get("compiler_surface_checks")
    if not isinstance(checks, list):
        return ["compiler surface coverage is absent"] if expected else []
    actual = [
        check.get("source_name") if isinstance(check, dict) else None
        for check in checks
    ]
    errors: list[str] = []
    if actual != expected:
        errors.append(
            "compiler_surface_checks must cover the compiler-declared and rule surfaces "
            "in exact order"
        )
    if verdict.get("alignment") == "aligned":
        unresolved = [
            check.get("source_name")
            for check in checks
            if isinstance(check, dict)
            and check.get("disposition")
            in {"missing_or_misaligned", "uncertain"}
        ]
        if unresolved:
            errors.append(
                "aligned verdict has unresolved compiler surface: "
                + ", ".join(str(name) for name in unresolved)
            )
    return errors


def normalize_source_unmatched_verdict(
    job: dict[str, Any], verdict: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    """Normalize a missed-match discovery into the unmatched-job protocol.

    A source-unmatched prompt asks the model to search the whole target tree, but
    the result remains a classification-only job.  Models sometimes perform the
    useful search and then return a normal paired verdict using the discovered
    target.  That loses the deterministic job identity and fails validation.

    Preserve the complete raw verdict as normalization evidence, while mapping
    the scored result to ``wrong_match/not_judged`` with a suggested target.  No
    semantic alignment claim or counterexample from the raw response is scored.
    """
    if job.get("kind") != "source_unmatched":
        return verdict, None
    errors = validate_verdict(job, verdict)
    relevant_errors = {
        "target_id does not match job",
        "source-unmatched job has invalid match_status",
        "source-unmatched job must use alignment=not_judged",
    }
    if not relevant_errors.intersection(errors):
        return verdict, None

    suggested = verdict.get("suggested_target")
    discovered_target_id = verdict.get("target_id")
    if discovered_target_id is None and isinstance(suggested, dict):
        discovered_target_id = suggested.get("id")
    if not isinstance(discovered_target_id, str) or not discovered_target_id:
        return verdict, None

    normalized = dict(verdict)
    normalized.update(
        {
            "source_id": job.get("source_id"),
            "target_id": None,
            "match_status": "wrong_match",
            "alignment": "not_judged",
            "failure_categories": ["wrong_item_match"],
            "interface_witness": {
                "status": "not_applicable",
                "kind": None,
                "source_interface": None,
                "target_interface": None,
                "explanation": "No semantic interface claim is being scored.",
                "compiler_validated": False,
            },
            "examples": [],
            "counterexamples": [],
            "suggested_target": {
                "id": discovered_target_id,
                "reason": (
                    "The read-only judge located this declaration while searching "
                    "the full translated directory for the source-unmatched item."
                ),
            },
            "target_disposition": None,
        }
    )
    return normalized, {
        "kind": "source_unmatched_discovered_target",
        "original_validation_errors": errors,
        "raw_verdict": verdict,
    }


def _run_command(
    command: list[str],
    *,
    cwd: Path,
    timeout: int,
    input_text: str | None = None,
) -> dict[str, Any]:
    try:
        process = subprocess.Popen(
            command,
            cwd=cwd,
            text=True,
            stdin=subprocess.PIPE if input_text is not None else subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
        try:
            stdout, stderr = process.communicate(input=input_text, timeout=timeout)
        except subprocess.TimeoutExpired:
            # Killing only the direct `codex` CLI process can leave its native
            # worker orphaned under PID 1.  Every invocation owns a fresh
            # session, so terminate the whole process group and collect all
            # pipes before returning the timeout result.
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                stdout, stderr = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = process.communicate()
            return {
                "command": command,
                "returncode": None,
                "stdout": (stdout or "")[-12000:],
                "stderr": (stderr or "")[-12000:],
                "timed_out": True,
            }
        return {
            "command": command,
            "returncode": process.returncode,
            "stdout": (stdout or "")[-12000:],
            "stderr": (stderr or "")[-12000:],
            "timed_out": False,
        }
    except OSError as exc:
        return {
            "command": command,
            "returncode": None,
            "stdout": "",
            "stderr": str(exc),
            "timed_out": False,
        }


def check_subscription_auth() -> dict[str, Any]:
    result = _run_command(
        ["codex", "login", "status"], cwd=Path.cwd(), timeout=30
    )
    output = result["stdout"] + "\n" + result["stderr"]
    chatgpt = result["returncode"] == 0 and "ChatGPT" in output
    if not chatgpt:
        raise PipelineError(
            "judge requires subscription authentication; "
            "`codex login status` did not report ChatGPT"
        )
    return {
        "mode": "subscription_cli",
        "status": normalize_space(output),
    }


class CodexJudgeRunner:
    """Subscription-backed, read-only Codex runner with schema-constrained output."""

    def __init__(
        self,
        task: TaskConfig,
        workspace: Path,
        *,
        model: str,
        reasoning_effort: str,
        timeout_seconds: int,
    ) -> None:
        self.task = task
        self.workspace = workspace
        self.model = model
        self.reasoning_effort = reasoning_effort
        self.timeout_seconds = timeout_seconds
        self.auth = check_subscription_auth()
        self.schema_path = workspace / JUDGE_DIRECTORY / JUDGE_SCHEMA
        write_json(self.schema_path, VERDICT_SCHEMA)

    def __call__(
        self,
        job: dict[str, Any],
        prompt: str,
        *,
        force: bool = False,
        prompt_version: str = PROMPT_VERSION,
        correction_feedback: str | None = None,
    ) -> dict[str, Any]:
        locks_dir = self.workspace / JUDGE_DIRECTORY / "locks"
        locks_dir.mkdir(parents=True, exist_ok=True)
        with (locks_dir / f"{job['key']}.lock").open("a+") as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
            return self._call_locked(
                job,
                prompt,
                force=force,
                prompt_version=prompt_version,
                correction_feedback=correction_feedback,
            )

    def _call_locked(
        self,
        job: dict[str, Any],
        prompt: str,
        *,
        force: bool,
        prompt_version: str,
        correction_feedback: str | None,
    ) -> dict[str, Any]:
        jobs_dir = self.workspace / JUDGE_DIRECTORY / "jobs"
        results_dir = self.workspace / JUDGE_DIRECTORY / "results"
        jobs_dir.mkdir(parents=True, exist_ok=True)
        results_dir.mkdir(parents=True, exist_ok=True)
        prompt_hash = sha256_bytes(prompt.encode("utf-8"))
        job_path = jobs_dir / f"{job['key']}.json"
        result_path = results_dir / f"{job['key']}.json"
        if result_path.is_file() and not force and correction_feedback is None:
            existing = read_json(result_path)
            if (
                existing.get("prompt_sha256") == prompt_hash
                and isinstance(existing.get("verdict"), dict)
            ):
                return existing
        write_json(
            job_path,
            {
                "version": JUDGE_VERSION,
                "prompt_version": prompt_version,
                "job": job,
                "prompt_sha256": prompt_hash,
                "prompt": prompt,
            },
        )
        attempt_prompt = prompt
        if correction_feedback:
            attempt_prompt += (
                "\n\nNON-NEGOTIABLE EXECUTION CORRECTION PASS\n"
                "The previous schema-valid evidence was independently executed "
                "and rejected. Return a complete replacement verdict. Correct "
                "the harnesses using the exact compiler diagnostics below. This "
                "is an evidence-repair pass: preserve the semantic verdict unless "
                "a diagnostic actually disproves its input/output relation. If "
                "you cannot produce the required verified evidence, follow "
                "the active protocol's fallback rule.\n"
                + correction_feedback
            )
        attempts: list[dict[str, Any]] = []
        normalization: dict[str, Any] | None = None
        verdict: dict[str, Any] | None = None
        validation_errors: list[str] = []
        command_result: dict[str, Any] = {}
        max_attempts = (
            1
            if correction_feedback is not None
            else (
                6
                if prompt_version
                in {
                    "semantic-alignment-v19",
                    "semantic-alignment-v20",
                    "semantic-alignment-v21",
                    "semantic-alignment-v22",
                    "semantic-alignment-v23",
                    "semantic-alignment-v24",
                    "semantic-alignment-v25",
                    "semantic-alignment-v26",
                    "semantic-alignment-v27",
                }
                else 2
                if prompt_version
                in {
                    "semantic-alignment-v12",
                    "semantic-alignment-v13",
                    "semantic-alignment-v16",
                    "semantic-alignment-v17",
                    "semantic-alignment-v18",
                }
                else 1
            )
        )
        for attempt_index in range(max_attempts):
            with tempfile.TemporaryDirectory(prefix="transformal-judge-") as directory:
                work_dir = Path(directory)
                raw_output = work_dir / "verdict.json"
                command_schema = self.schema_path
                command_output = raw_output
                if blind_eval_enabled():
                    command_schema = work_dir / "verdict-schema.json"
                    shutil.copy2(self.schema_path, command_schema)
                command = [
                    "codex",
                    "exec",
                    "--ephemeral",
                    "--skip-git-repo-check",
                    "--ignore-user-config",
                    "--sandbox",
                    "read-only",
                    "--cd",
                    str(self.task.source.root),
                    "--add-dir",
                    str(self.task.target.project),
                    "--model",
                    self.model,
                    "--config",
                    f'model_reasoning_effort="{self.reasoning_effort}"',
                    "--output-schema",
                    (
                        "/tmp/transformal-blind-work/verdict-schema.json"
                        if blind_eval_enabled()
                        else str(command_schema)
                    ),
                    "--output-last-message",
                    (
                        "/tmp/transformal-blind-work/verdict.json"
                        if blind_eval_enabled()
                        else str(command_output)
                    ),
                    "-",
                ]
                with blind_eval_command(
                    source_root=self.task.source.root,
                    target_root=self.task.target.project,
                    work_dir=work_dir,
                    inner_args=command,
                    compiler_command=self.task.source.compiler_command,
                ) as executable_command:
                    command_result = _run_command(
                        executable_command,
                        cwd=self.task.source.root,
                        timeout=self.timeout_seconds,
                        input_text=attempt_prompt,
                    )
                verdict = None
                parse_error: str | None = None
                if raw_output.is_file():
                    try:
                        value = json.loads(raw_output.read_text(encoding="utf-8"))
                        if isinstance(value, dict):
                            verdict = value
                        else:
                            parse_error = "model output is not a JSON object"
                    except json.JSONDecodeError as exc:
                        parse_error = f"invalid model JSON: {exc}"
                else:
                    parse_error = "Codex did not write a final verdict"
            normalization = None
            if verdict is not None:
                verdict, normalization = normalize_source_unmatched_verdict(
                    job, verdict
                )
                if prompt_version == "semantic-alignment-v16":
                    normalize_typed_witness_bindings(verdict)
            validation_errors = (
                [parse_error]
                if parse_error is not None
                else validate_verdict(
                    job, verdict or {}, prompt_version=prompt_version
                )
            )
            attempts.append(
                {
                    "attempt": attempt_index + 1,
                    "prompt_sha256": sha256_bytes(
                        attempt_prompt.encode("utf-8")
                    ),
                    "command": command_result,
                    "validation_errors": validation_errors,
                    "verdict": verdict,
                }
            )
            if not validation_errors or attempt_index + 1 == max_attempts:
                break
            attempt_prompt = prompt + (
                "\n\nNON-NEGOTIABLE CORRECTION PASS\n"
                f"The previous response was rejected by the deterministic {prompt_version} "
                "validator. Return a complete replacement JSON verdict, not a "
                "patch. Fix every listed error. An aligned replacement must "
                f"contain at least {'one' if aligned_example_requirement(prompt_version) == 1 else 'three'} complete two-sided example(s); a "
                "not_aligned replacement must contain at least one complete "
                "two-sided counterexample; otherwise follow the active "
                "protocol's fallback rule.\n"
                "VALIDATION ERRORS:\n"
                + json.dumps(validation_errors, ensure_ascii=False, indent=2)
                + "\nPREVIOUS VERDICT:\n"
                + json.dumps(verdict, ensure_ascii=False, indent=2)
            )
        envelope = {
            "version": JUDGE_VERSION,
            "job_key": job["key"],
            "prompt_sha256": prompt_hash,
            "runner": {
                "backend": "codex_subscription",
                "model": self.model,
                "reasoning_effort": self.reasoning_effort,
                "auth": self.auth,
            },
            "command": command_result,
            "attempts": attempts,
            "verdict": verdict,
            "validation_errors": validation_errors,
        }
        if normalization is not None:
            envelope["normalization"] = normalization
        write_json(result_path, envelope)
        return envelope

    def retry_with_feedback(
        self,
        job: dict[str, Any],
        prompt: str,
        feedback: str,
        *,
        prompt_version: str,
    ) -> dict[str, Any]:
        return self(
            job,
            prompt,
            force=True,
            prompt_version=prompt_version,
            correction_feedback=feedback,
        )


def run_judge_jobs(
    task: TaskConfig,
    source_index: dict[str, Any],
    target_index: dict[str, Any],
    plan: dict[str, Any],
    runner: Callable[..., dict[str, Any]],
    *,
    workspace: Path,
    max_workers: int,
    limit: int | None = None,
    job_keys: list[str] | None = None,
    source_ids: list[str] | None = None,
    force: bool = False,
    max_execution_retries: int | None = None,
) -> list[dict[str, Any]]:
    prompt_version = plan.get("prompt_version", "semantic-alignment-v1")
    if prompt_version not in SUPPORTED_PROMPT_VERSIONS:
        raise PipelineError(
            f"unsupported judge prompt version: {prompt_version}"
        )
    source_by_id = {
        item["id"]: item for item in source_index.get("declarations", [])
    }
    target_by_id = {
        item["id"]: item for item in target_index.get("declarations", [])
    }
    attach_relational_dependency_context(source_by_id, target_by_id)
    jobs = plan["jobs"]
    if job_keys is not None:
        requested = set(job_keys)
        jobs = [job for job in jobs if job["key"] in requested]
        missing = sorted(requested - {job["key"] for job in jobs})
        if missing:
            raise PipelineError("unknown judge job keys: " + ", ".join(missing))
    elif source_ids is not None:
        requested = set(source_ids)
        jobs = [job for job in jobs if job.get("source_id") in requested]
        missing = sorted(requested - {job.get("source_id") for job in jobs})
        if missing:
            raise PipelineError("source ids have no judge job: " + ", ".join(missing))
    elif limit is not None:
        jobs = jobs[:limit]

    def deterministic_target_unmatched(
        job: dict[str, Any], prompt: str
    ) -> dict[str, Any]:
        source_id = job.get("source_id")
        target_id = job.get("target_id")
        if job["kind"] == "target_unmatched":
            verdict = {
                "source_id": None,
                "target_id": target_id,
                "match_status": "target_unmatched",
                "alignment": "not_judged",
                "confidence": 1.0,
                "source_summary": "No source declaration was matched.",
                "target_summary": (
                    "The deterministic matcher found no corresponding source "
                    "declaration above its configured threshold."
                ),
                "failure_categories": [],
                "differences": [
                    "The target declaration has no deterministic source match."
                ],
                "interface_witness": {
                    "status": "not_applicable",
                    "kind": None,
                    "source_interface": None,
                    "target_interface": None,
                    "explanation": "There is no paired source interface.",
                    "compiler_validated": False,
                },
                "examples": [],
                "counterexamples": [],
                "suggested_target": None,
                "target_disposition": "uncertain",
                "evidence": [],
                "compiler_surface_checks": [],
            }
        else:
            raise PipelineError(
                "deterministic target-unmatched handler received "
                f"{job['kind']!r}"
            )
        errors = validate_verdict(job, verdict)
        envelope = {
            "version": JUDGE_VERSION,
            "job_key": job["key"],
            "prompt_sha256": sha256_bytes(prompt.encode("utf-8")),
            "runner": {
                "backend": "deterministic_unmatched",
                "model": None,
                "reasoning_effort": None,
                "auth": None,
            },
            "command": None,
            "verdict": verdict,
            "validation_errors": errors,
        }
        results_dir = workspace / JUDGE_DIRECTORY / "results"
        results_dir.mkdir(parents=True, exist_ok=True)
        write_json(results_dir / f"{job['key']}.json", envelope)
        return envelope

    def execute(job: dict[str, Any]) -> dict[str, Any]:
        prompt = render_judge_prompt(
            task,
            job,
            source_by_id.get(job.get("source_id")),
            target_by_id.get(job.get("target_id")),
            prompt_version=prompt_version,
        )
        if job["kind"] == "target_unmatched":
            return deterministic_target_unmatched(job, prompt)

        def postprocess(envelope: dict[str, Any]) -> dict[str, Any]:
            verdict = envelope.get("verdict")
            if not isinstance(verdict, dict):
                return envelope
            if prompt_version in {
                "semantic-alignment-v16",
                "semantic-alignment-v17",
                "semantic-alignment-v18",
                "semantic-alignment-v19",
                "semantic-alignment-v20",
                "semantic-alignment-v21",
                "semantic-alignment-v22",
                "semantic-alignment-v23",
                "semantic-alignment-v24",
                "semantic-alignment-v25",
                "semantic-alignment-v26",
                "semantic-alignment-v27",
            }:
                normalize_typed_witness_bindings(verdict)
            # Never trust cached validation metadata: every backend is checked
            # against the current schema and anti-abstention policy on replay.
            envelope["validation_errors"] = validate_verdict(
                job, verdict, prompt_version=prompt_version
            )
            if prompt_version in {
                "semantic-alignment-v5",
                "semantic-alignment-v6",
                "semantic-alignment-v7",
                "semantic-alignment-v8",
                "semantic-alignment-v9",
                "semantic-alignment-v10",
                "semantic-alignment-v11",
                "semantic-alignment-v12",
                "semantic-alignment-v13",
            }:
                envelope["validation_errors"].extend(
                    _validate_compiler_surface_coverage(
                        source_by_id.get(job.get("source_id")), verdict
                    )
                )
            if not envelope["validation_errors"]:
                observation_verification = envelope.get(
                    "observation_verification"
                )
                if (
                    not isinstance(observation_verification, dict)
                    or observation_verification.get("verdict_sha256")
                    != sha256_json(verdict)
                    or observation_verification.get("errors")
                ):
                    observation_verification = verify_verdict_observations(
                        task,
                        verdict,
                        source_by_id.get(job.get("source_id")),
                        target_by_id.get(job.get("target_id")),
                        timeout=task.acceptance.build_timeout_seconds,
                    )
                envelope["observation_verification"] = observation_verification
                envelope["validation_errors"].extend(
                    observation_verification["errors"]
                )
            write_json(
                workspace / JUDGE_DIRECTORY / "results" / f"{job['key']}.json",
                envelope,
            )
            return envelope

        envelope = postprocess(
            runner(
                job,
                prompt,
                force=force,
                prompt_version=prompt_version,
            )
        )
        retry_method = getattr(runner, "retry_with_feedback", None)
        execution_retries: list[dict[str, Any]] = []
        retry_limit = (
            3
            if prompt_version
            in {
                "semantic-alignment-v21",
                "semantic-alignment-v22",
                "semantic-alignment-v23",
                "semantic-alignment-v24",
                "semantic-alignment-v25",
                "semantic-alignment-v26",
                "semantic-alignment-v27",
            }
            else 1
        )
        if max_execution_retries is not None:
            retry_limit = max_execution_retries
        for _ in range(retry_limit):
            observation_verification = envelope.get("observation_verification")
            if not (
                callable(retry_method)
                and isinstance(observation_verification, dict)
                and observation_verification.get("errors")
            ):
                break
            diagnostics = []
            for record in observation_verification.get("records", []):
                verification = record.get("verification") or {}
                diagnostic = {"id": verification.get("id")}
                for side_name in ("source", "target"):
                    side = verification.get(side_name) or {}
                    result = side.get("result") or {}
                    diagnostic[side_name] = {
                        "status": side.get("status"),
                        "reason": side.get("reason"),
                        "binding_errors": side.get("binding_errors"),
                        "stdout": str(result.get("stdout") or "")[-3000:],
                        "stderr": str(result.get("stderr") or "")[-3000:],
                    }
                diagnostics.append(diagnostic)
            feedback = json.dumps(
                {
                    "validation_errors": observation_verification["errors"],
                    "compiler_diagnostics": diagnostics,
                    "previous_verdict": envelope.get("verdict"),
                },
                ensure_ascii=False,
                indent=2,
            )
            failed_attempt = {
                "validation_errors": envelope.get("validation_errors"),
                "observation_verification": observation_verification,
                "verdict": envelope.get("verdict"),
            }
            execution_retries.append(failed_attempt)
            envelope = postprocess(
                retry_method(
                    job,
                    prompt,
                    feedback,
                    prompt_version=prompt_version,
                )
            )
            envelope["execution_retry"] = execution_retries[0]
            envelope["execution_retries"] = execution_retries
            write_json(
                workspace / JUDGE_DIRECTORY / "results" / f"{job['key']}.json",
                envelope,
            )
        return envelope

    results: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(execute, job): job for job in jobs}
        for future in as_completed(futures):
            job = futures[future]
            try:
                results.append(future.result())
            except Exception as exc:  # preserve every failed judge as evidence
                envelope = {
                    "version": JUDGE_VERSION,
                    "job_key": job["key"],
                    "prompt_sha256": None,
                    "runner": None,
                    "command": None,
                    "verdict": None,
                    "validation_errors": [f"judge runner failed: {exc}"],
                }
                results.append(envelope)
                write_json(
                    workspace / JUDGE_DIRECTORY / "results" / f"{job['key']}.json",
                    envelope,
                )
    return sorted(results, key=lambda item: item["job_key"])


def compile_translation(task: TaskConfig) -> dict[str, Any]:
    command = ["lake", "build", *task.target.build_targets]
    result = _run_command(
        command,
        cwd=task.target.project,
        timeout=task.acceptance.build_timeout_seconds,
    )
    return {
        "status": "passed" if result["returncode"] == 0 else "failed",
        "result": result,
    }


def compile_target_modules(
    task: TaskConfig,
    target_index: dict[str, Any],
    target_ids: Iterable[str],
    *,
    max_workers: int = 4,
) -> dict[str, Any]:
    """Compile only Lean modules owned by one semantic judge scope."""
    by_id = {
        item["id"]: item for item in target_index.get("declarations", [])
    }
    modules = sorted(
        {
            module_name_for_path(by_id[target_id]["target_file"])
            for target_id in target_ids
            if target_id in by_id and by_id[target_id].get("role") != "test"
        }
    )
    if not modules:
        return {
            "status": "not_applicable",
            "modules": [],
            "results": [],
        }

    def compile_one(module: str) -> dict[str, Any]:
        result = _run_command(
            ["lake", "build", module],
            cwd=task.target.project,
            timeout=task.acceptance.build_timeout_seconds,
        )
        return {
            "module": module,
            "status": "passed" if result["returncode"] == 0 else "failed",
            "result": result,
        }

    results: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=min(max_workers, len(modules))) as executor:
        futures = {executor.submit(compile_one, module): module for module in modules}
        for future in as_completed(futures):
            module = futures[future]
            try:
                results.append(future.result())
            except Exception as exc:
                results.append(
                    {
                        "module": module,
                        "status": "failed",
                        "result": {
                            "command": ["lake", "build", module],
                            "returncode": None,
                            "stdout": "",
                            "stderr": str(exc),
                            "timed_out": False,
                        },
                    }
                )
    results.sort(key=lambda item: item["module"])
    return {
        "status": (
            "passed"
            if all(item["status"] == "passed" for item in results)
            else "failed"
        ),
        "modules": modules,
        "results": results,
    }


def _coq_project_arguments(repository: Path) -> list[str]:
    project = next(
        (
            repository / filename
            for filename in ("_RocqProject", "_CoqProject")
            if (repository / filename).is_file()
        ),
        None,
    )
    if project is None:
        return []
    tokens = project.read_text(encoding="utf-8").split()
    result: list[str] = []
    index = 0
    while index < len(tokens):
        if tokens[index] in {"-Q", "-R"} and index + 2 < len(tokens):
            result.extend(
                [
                    tokens[index],
                    str((repository / tokens[index + 1]).resolve()),
                    tokens[index + 2],
                ]
            )
            index += 3
        else:
            index += 1
    return result


def _isabelle_command(task: TaskConfig) -> list[str]:
    if task.source.compiler_command:
        return list(task.source.compiler_command)
    executable = shutil.which("isabelle")
    return [executable] if executable else []


def _isabelle_session(task: TaskConfig) -> str:
    if task.source.session:
        return task.source.session
    root = task.source.root / "ROOT"
    if root.is_file():
        match = re.search(
            r'(?m)^\s*session\s+(?:"([^\"]+)"|(\S+))\s*=',
            root.read_text(encoding="utf-8"),
        )
        if match:
            return match.group(1) or match.group(2)
    return "HOL"


def verify_counterexample_test(
    task: TaskConfig, test: dict[str, Any] | None, *, timeout: int = 120
) -> dict[str, Any]:
    if test is None:
        return {"status": "absent"}
    language = test["language"]
    if language == "lean":
        executable = "lean"
        lake = shutil.which("lake")
        if lake is None:
            elan_lake = Path.home() / ".elan/bin/lake"
            if elan_lake.is_file() and os.access(elan_lake, os.X_OK):
                lake = str(elan_lake)
        command_prefix = [lake, "env", "lean"] if lake else []
    elif language == "isabelle":
        executable = "isabelle"
        command_prefix = _isabelle_command(task)
    elif task.source.compiler_command:
        executable = "configured Coq compiler"
        command_prefix = list(task.source.compiler_command)
    elif shutil.which("coqc") is not None:
        executable = "coqc"
        command_prefix = ["coqc"]
    elif shutil.which("rocq") is not None:
        executable = "rocq compile"
        command_prefix = ["rocq", "compile"]
    elif shutil.which("opam") is not None:
        executable = "opam exec -- coqc"
        command_prefix = ["opam", "exec", "--", "coqc"]
    else:
        executable = "coqc or rocq compile"
        command_prefix = []
    if not command_prefix:
        return {
            "status": "unavailable",
            "language": language,
            "reason": f"{executable} is not installed",
        }
    suffix = {"lean": ".lean", "isabelle": ".thy"}.get(language, ".v")
    with tempfile.TemporaryDirectory(prefix="transformal-counterexample-") as directory:
        path = Path(directory) / f"Counterexample{suffix}"
        code = test["code"]
        policy_violations = get_policy(language).test_violations(code)
        if policy_violations:
            return {
                "status": "rejected",
                "language": language,
                "reason": "counterexample test uses forbidden trust constructs",
                "policy_violations": policy_violations,
            }
        if language == "isabelle":
            theory_header = re.search(
                r'(?m)^(?P<prefix>\s*theory\s+)(?P<name>"[^"]+"|[A-Za-z0-9_\'.-]+)',
                code,
            )
            if theory_header:
                theory_name = theory_header.group("name").strip('"')
                code = (
                    code[: theory_header.start()]
                    + theory_header.group("prefix")
                    + "Counterexample"
                    + code[theory_header.end() :]
                )
                code = re.sub(
                    rf"(?<![A-Za-z0-9_'.-]){re.escape(theory_name)}\.",
                    "Counterexample.",
                    code,
                )
            else:
                code = "theory Counterexample imports Main begin\n" + code + "\nend\n"
        path.write_text(code, encoding="utf-8")
        if language == "lean":
            command = [*command_prefix, str(path)]
            cwd = task.target.project
        elif language == "isabelle":
            parent = _isabelle_session(task)
            session = "Transformal_Counterexample_" + sha256_bytes(
                directory.encode("utf-8")
            )[:12]
            root = Path(directory) / "ROOT"
            root.write_text(
                f'session {session} = "{parent}" +\n'
                "  theories Counterexample\n",
                encoding="utf-8",
            )
            command = [*command_prefix, "build", "-o", "threads=1"]
            for session_dir in task.source.session_dirs:
                command.extend(["-d", str(session_dir)])
            command.extend(
                [
                    "-d",
                    str(task.source.root),
                    "-D",
                    directory,
                    session,
                ]
            )
            cwd = task.source.repository
        else:
            command = [
                *command_prefix,
                *_coq_project_arguments(task.source.repository),
                str(path),
            ]
            cwd = task.source.repository
        result = _run_command(command, cwd=cwd, timeout=timeout)
    if result["timed_out"]:
        return {
            "status": "timed_out",
            "language": language,
            "reason": f"compiler exceeded the {timeout}-second verification timeout",
            "expected_result": test["expected_result"],
            "actual_result": None,
            "result": result,
        }
    actual = "pass" if result["returncode"] == 0 else "fail"
    if actual == "fail":
        status = (
            "observed_failure"
            if test["expected_result"] == "fail"
            else "unverified"
        )
    else:
        status = (
            "verified" if test["expected_result"] == "pass" else "contradicted"
        )
    return {
        "status": status,
        "language": language,
        "expected_result": test["expected_result"],
        "actual_result": actual,
        "verification_note": (
            "A nonzero compiler exit observes failure but cannot distinguish the "
            "intended semantic rejection from syntax, import, or environment errors. "
            "Use a passing language-native negative assertion (for example Coq "
            "`Fail`, an Isabelle proposition that proves the negation, or Lean "
            "`#guard_msgs`) for compiler-verified negative evidence."
            if status in {"observed_failure", "unverified"}
            else None
        ),
        "result": result,
    }


def _append_claim_binding(
    language: str,
    code: str,
    entrypoint: str,
    invocation: str,
    claim: str,
) -> str:
    invocation_is_in_claim = normalize_space(invocation) in normalize_space(claim)
    if language == "coq":
        bindings = [f"Check ({entrypoint} : {claim})."]
        if not invocation_is_in_claim:
            bindings.append(f"Check ({invocation} : {claim}).")
        return code.rstrip() + "\n\n" + "\n".join(bindings) + "\n"
    if language == "lean":
        bindings = [f"#check ({entrypoint} : {claim})"]
        if not invocation_is_in_claim:
            bindings.append(f"#check ({invocation} : {claim})")
        return code.rstrip() + "\n\n" + "\n".join(bindings) + "\n"
    theory_header = re.search(
        r'(?m)^\s*theory\s+(?:"([^"]+)"|([A-Za-z0-9_\'.-]+))', code
    )
    isabelle_entrypoint = entrypoint
    if theory_header:
        theory_name = theory_header.group(1) or theory_header.group(2)
        if isabelle_entrypoint.startswith(f"{theory_name}."):
            isabelle_entrypoint = isabelle_entrypoint[len(theory_name) + 1 :]
    # Isabelle symbol escapes such as ``\<union>`` are source syntax, not
    # string-runtime backslashes.  Doubling them produces malformed theory
    # text.  Only protect literal quote delimiters here.
    escaped_claim = claim.replace('"', '\\"')
    bindings = (
        "\nlemma TransformalHarnessBinding: "
        f'"{escaped_claim}" using {isabelle_entrypoint} by assumption\n'
    )
    if not invocation_is_in_claim:
        bindings += (
            "lemma TransformalInvocationBinding: "
            f'"{escaped_claim}" using {invocation} by assumption\n'
        )
    end_matches = list(re.finditer(r"(?m)^\s*end\s*$", code))
    if end_matches:
        position = end_matches[-1].start()
        return code[:position].rstrip() + "\n" + bindings + code[position:]
    return code.rstrip() + bindings


_EVALUATION_BEGIN = "__TRANSFORMAL_OBSERVATION_BEGIN__"
_EVALUATION_END = "__TRANSFORMAL_OBSERVATION_END__"


def _append_evaluation_probe(
    language: str,
    code: str,
    invocation: str,
    output_expression: str,
) -> str:
    """Append a pipeline-owned evaluation of the exact judged invocation."""
    if language == "lean":
        probe = (
            f'\n#eval IO.println "{_EVALUATION_BEGIN}"\n'
            f"#eval ({invocation})\n"
            f'#eval IO.println "{_EVALUATION_END}"\n'
        )
        return code.rstrip() + "\n" + probe
    if language == "coq":
        probe = (
            "\nGoal True.\n"
            f'  idtac "{_EVALUATION_BEGIN}".\n'
            f"  let observed := (eval cbv in ({invocation})) in idtac observed.\n"
            f'  idtac "{_EVALUATION_END}".\n'
            "  exact I.\nQed.\n"
        )
        return code.rstrip() + "\n" + probe
    escaped_equality = (
        f"({invocation}) = ({output_expression})"
    ).replace("\\", "\\\\").replace('"', '\\"')
    probe = (
        "\nlemma TransformalEvaluationBinding: "
        f'"{escaped_equality}" by eval\n'
    )
    end_matches = list(re.finditer(r"(?m)^\s*end\s*$", code))
    if end_matches:
        position = end_matches[-1].start()
        return code[:position].rstrip() + "\n" + probe + code[position:]
    return code.rstrip() + probe


def _evaluation_output_region(process_output: str) -> str | None:
    begin = process_output.rfind(_EVALUATION_BEGIN)
    end = process_output.rfind(_EVALUATION_END)
    if begin < 0 or end < 0 or end <= begin:
        return None
    return process_output[begin + len(_EVALUATION_BEGIN) : end].strip()


def _strip_nested_block_comments(code: str, opening: str, closing: str) -> str:
    result = list(code)
    depth = 0
    index = 0
    while index < len(code):
        if code.startswith(opening, index):
            depth += 1
            for position in range(index, index + len(opening)):
                result[position] = " "
            index += len(opening)
            continue
        if depth and code.startswith(closing, index):
            for position in range(index, index + len(closing)):
                result[position] = " "
            depth -= 1
            index += len(closing)
            continue
        if depth:
            result[index] = "\n" if code[index] == "\n" else " "
        index += 1
    return "".join(result)


def _code_without_comments(language: str, code: str) -> str:
    if language == "lean":
        return mask_lean_comments_and_strings(code)
    return _strip_nested_block_comments(code, "(*", "*)")


def _code_without_comments_preserving_strings(language: str, code: str) -> str:
    """Mask comments while retaining literals needed for exact call binding."""
    result = list(code)
    opening, closing = (("/-", "-/") if language == "lean" else ("(*", "*)"))
    depth = 0
    in_string = False
    index = 0
    while index < len(code):
        if depth:
            if code.startswith(opening, index):
                depth += 1
                for position in range(index, index + len(opening)):
                    result[position] = " "
                index += len(opening)
                continue
            if code.startswith(closing, index):
                for position in range(index, index + len(closing)):
                    result[position] = " "
                depth -= 1
                index += len(closing)
                continue
            result[index] = "\n" if code[index] == "\n" else " "
            index += 1
            continue
        if in_string:
            if code[index] == "\\" and index + 1 < len(code):
                index += 2
                continue
            if code[index] == '"':
                if language != "lean" and index + 1 < len(code) and code[index + 1] == '"':
                    index += 2
                    continue
                in_string = False
            index += 1
            continue
        if code[index] == '"':
            in_string = True
            index += 1
            continue
        if language == "lean" and code.startswith("--", index):
            end = code.find("\n", index)
            end = len(code) if end < 0 else end
            for position in range(index, end):
                result[position] = " "
            index = end
            continue
        if code.startswith(opening, index):
            depth = 1
            for position in range(index, index + len(opening)):
                result[position] = " "
            index += len(opening)
            continue
        index += 1
    return "".join(result)


def verify_observation_side(
    task: TaskConfig,
    side: dict[str, Any],
    *,
    expected_language: str,
    expected_subjects: set[str],
    controlled_declaration: str | None = None,
    allow_qualified_parameter_implementation: bool = False,
    timeout: int = 120,
) -> dict[str, Any]:
    run = side.get("run") or {}
    language = run.get("language")
    subject = side.get("subject")
    input_expression = (side.get("input") or {}).get("expression")
    output_expression = (side.get("output") or {}).get("expression")
    invocation = run.get("invocation")
    claim = run.get("claim")
    code = run.get("code")
    binding_errors: list[str] = []
    if language != expected_language:
        binding_errors.append(
            f"run language {language!r} does not match {expected_language!r}"
        )
    if subject not in expected_subjects:
        binding_errors.append(
            "subject is not the compiler-indexed judged declaration: "
            f"{subject!r} not in {sorted(expected_subjects)!r}"
        )
    if not isinstance(code, str) or not code.strip():
        binding_errors.append("run code is empty")
    mode = run.get("mode")
    if not isinstance(claim, str) or not claim.strip():
        binding_errors.append("run claim is empty")
    elif mode == "prove":
        if (
            not isinstance(output_expression, str)
            or normalize_space(output_expression) != normalize_space(claim)
        ):
            binding_errors.append(
                "prove output.expression must exactly equal run claim"
            )
    elif mode == "evaluate" and isinstance(invocation, str):
        if normalize_space(claim) != normalize_space(invocation):
            binding_errors.append("evaluate run claim must equal invocation")
    if not isinstance(invocation, str) or not invocation.strip():
        binding_errors.append("run invocation is empty")
    else:
        if isinstance(subject, str) and not _references_subject(invocation, subject):
            binding_errors.append("run invocation does not call its judged subject")
        if (
            not isinstance(input_expression, str)
            or not isinstance(subject, str)
            or not _invocation_binds_complete_input(
                invocation, subject, input_expression
            )
        ):
            binding_errors.append(
                "run input.expression is not the complete subject application input"
            )
    executable_surface = (
        _code_without_comments(str(language), code)
        if isinstance(code, str)
        else ""
    )
    literal_binding_surface = (
        _code_without_comments_preserving_strings(str(language), code)
        if isinstance(code, str)
        else ""
    )
    if isinstance(subject, str):
        if not _references_subject(executable_surface, subject):
            binding_errors.append("run code does not reference its judged subject")
        elif _declares_subject(str(language), executable_surface, subject):
            qualified_parameter = (
                allow_qualified_parameter_implementation
                and isinstance(invocation, str)
                and "." in invocation
                and re.search(r"(?mi)^\s*Module\s+", executable_surface)
            )
            if controlled_declaration is None:
                if not qualified_parameter:
                    binding_errors.append("run code locally shadows its judged subject")
            elif normalize_space(controlled_declaration) not in normalize_space(executable_surface):
                binding_errors.append(
                    "controlled local declaration does not match indexed target_text"
                )
    if isinstance(invocation, str) and normalize_space(invocation) not in normalize_space(
        literal_binding_surface
    ):
        binding_errors.append("run code does not contain its invocation")
    executable_code = code if isinstance(code, str) else ""
    if mode == "prove":
        entrypoint = run.get("entrypoint")
        if not isinstance(entrypoint, str) or not entrypoint.strip():
            binding_errors.append("prove run has no entrypoint")
        elif isinstance(claim, str):
            executable_code = _append_claim_binding(
                str(language),
                executable_code,
                entrypoint,
                str(invocation),
                claim,
            )
    elif mode == "evaluate":
        if not run.get("expected_stdout"):
            binding_errors.append("evaluate run has no expected_stdout")
        if isinstance(claim, str) and normalize_space(claim) not in normalize_space(
            literal_binding_surface
        ):
            binding_errors.append(
                "evaluate run code does not contain its claimed expression"
            )
        if str(run.get("expected_stdout")) != str(output_expression):
            binding_errors.append(
                "evaluate expected_stdout must equal output.expression"
            )
        if isinstance(invocation, str):
            executable_code = _append_evaluation_probe(
                str(language), executable_code, invocation, str(output_expression)
            )
    else:
        binding_errors.append(f"unsupported run mode: {mode!r}")
    if binding_errors:
        return {
            "status": "rejected",
            "binding_errors": binding_errors,
            "input_expression": input_expression,
            "claimed_output": output_expression,
        }
    verification = verify_counterexample_test(
        task,
        {
            "language": language,
            "code": executable_code,
            "expected_result": "pass",
        },
        timeout=timeout,
    )
    status = verification.get("status")
    observed_output: str | None = None
    if status == "verified" and mode == "prove":
        observed_output = str(output_expression)
    elif status == "verified" and mode == "evaluate":
        expected_stdout = str(run["expected_stdout"])
        result = verification.get("result") or {}
        process_output = str(result.get("stdout") or "") + str(
            result.get("stderr") or ""
        )
        if language == "isabelle":
            output_region = str(output_expression)
            verification["pipeline_evaluation_claim"] = (
                f"({invocation}) = ({output_expression})"
            )
            verification["pipeline_evaluation_method"] = "by eval"
        else:
            output_region = _evaluation_output_region(process_output)
            verification["pipeline_evaluation_output"] = output_region
        if output_region is None:
            status = "contradicted"
            verification["verification_note"] = (
                "pipeline-owned invocation evaluation markers were absent"
            )
        elif normalize_space(expected_stdout) != normalize_space(output_region):
            status = "contradicted"
            verification["verification_note"] = (
                "the pipeline-owned exact invocation evaluation output does not "
                "equal expected_stdout"
            )
        else:
            observed_output = output_region
    return {
        **verification,
        "status": status,
        "subject": subject,
        "input_expression": input_expression,
        "invocation": invocation,
        "claimed_output": output_expression,
        "observed_output": observed_output,
        "claim_sha256": sha256_bytes(str(claim).encode("utf-8")),
        "code_sha256": sha256_bytes(executable_code.encode("utf-8")),
        "binding_status": "verified",
    }


def verify_observation_pair(
    task: TaskConfig,
    observation: dict[str, Any],
    source_item: dict[str, Any] | None,
    target_item: dict[str, Any] | None,
    *,
    timeout: int = 120,
) -> dict[str, Any]:
    source_subjects = _indexed_subjects(source_item)
    target_subjects = _indexed_subjects(target_item)
    source = verify_observation_side(
        task,
        observation.get("source") or {},
        expected_language=task.source.language,
        expected_subjects=source_subjects,
        allow_qualified_parameter_implementation=bool(
            source_item and source_item.get("kind") == "Parameter"
        ),
        timeout=timeout,
    )
    target = verify_observation_side(
        task,
        observation.get("target") or {},
        expected_language="lean",
        expected_subjects=target_subjects,
        controlled_declaration=(
            str(target_item.get("target_text"))
            if target_item
            and target_item.get("role") == "controlled_semantic_mutant"
            and target_item.get("target_text")
            else None
        ),
        timeout=timeout,
    )
    return {
        "id": observation.get("id"),
        "source": source,
        "target": target,
        "input_alignment": observation.get("input_alignment"),
        "output_alignment": observation.get("output_alignment"),
        "chain_verified": (
            source.get("status") == "verified"
            and target.get("status") == "verified"
        ),
    }


def verify_verdict_observations(
    task: TaskConfig,
    verdict: dict[str, Any],
    source_item: dict[str, Any] | None,
    target_item: dict[str, Any] | None,
    *,
    timeout: int = 120,
) -> dict[str, Any]:
    records: list[dict[str, Any]] = []
    for kind, observations in (
        ("example", verdict.get("examples") or []),
        ("counterexample", verdict.get("counterexamples") or []),
    ):
        for observation in observations:
            records.append(
                {
                    "kind": kind,
                    "observation": observation,
                    "verification": verify_observation_pair(
                        task,
                        observation,
                        source_item,
                        target_item,
                        timeout=timeout,
                    ),
                }
            )
    errors = [
        "unverified input-to-output observation chain: "
        f"{record['kind']} {record['observation'].get('id')}: source="
        f"{record['verification']['source'].get('status')}, target="
        f"{record['verification']['target'].get('status')}"
        for record in records
        if not record["verification"]["chain_verified"]
    ]
    return {
        "version": 1,
        "verdict_sha256": sha256_json(verdict),
        "records": records,
        "errors": errors,
        "all_chains_verified": not errors,
    }


def load_judge_results(workspace: Path) -> dict[str, dict[str, Any]]:
    directory = workspace / JUDGE_DIRECTORY / "results"
    if not directory.is_dir():
        return {}
    return {
        path.stem: read_json(path)
        for path in sorted(directory.glob("*.json"))
    }


def aggregate_judge_report(
    task: TaskConfig,
    source_index: dict[str, Any],
    target_index: dict[str, Any],
    plan: dict[str, Any],
    compile_result: dict[str, Any],
    results: dict[str, dict[str, Any]],
    *,
    prompt_hasher: Callable[[dict[str, Any], str], str] | None = None,
) -> dict[str, Any]:
    prompt_version = plan.get("prompt_version", "semantic-alignment-v1")
    if prompt_version not in SUPPORTED_PROMPT_VERSIONS:
        raise PipelineError(
            f"unsupported judge prompt version: {prompt_version}"
        )
    jobs_by_key = {item["key"]: item for item in plan["jobs"]}
    source_by_id = {
        item["id"]: item for item in source_index.get("declarations", [])
    }
    target_by_id = {
        item["id"]: item for item in target_index.get("declarations", [])
    }
    attach_relational_dependency_context(source_by_id, target_by_id)
    valid_verdicts: list[tuple[dict[str, Any], dict[str, Any]]] = []
    invalid_results: list[dict[str, Any]] = []
    examples: list[dict[str, Any]] = []
    counterexamples: list[dict[str, Any]] = []
    failure_categories: Counter[str] = Counter()
    alignment_counts: Counter[str] = Counter()
    match_status_counts: Counter[str] = Counter()
    target_dispositions: Counter[str] = Counter()
    for key, envelope in sorted(results.items()):
        job = jobs_by_key.get(key)
        if job is None:
            invalid_results.append(
                {"job_key": key, "errors": ["result has no planned job"]}
            )
            continue
        expected_prompt = render_judge_prompt(
            task,
            job,
            source_by_id.get(job.get("source_id")),
            target_by_id.get(job.get("target_id")),
            prompt_version=prompt_version,
        )
        expected_prompt_hash = (
            prompt_hasher(job, expected_prompt)
            if prompt_hasher
            else sha256_bytes(expected_prompt.encode("utf-8"))
        )
        if envelope.get("prompt_sha256") != expected_prompt_hash:
            invalid_results.append(
                {
                    "job_key": key,
                    "errors": [
                        "result prompt hash does not match the current "
                        "source/target judge job"
                    ],
                }
            )
            continue
        verdict = envelope.get("verdict")
        errors = (
            validate_verdict(job, verdict, prompt_version=prompt_version)
            if isinstance(verdict, dict)
            else ["result does not contain a verdict object"]
        )
        if errors or not isinstance(verdict, dict):
            invalid_result = {"job_key": key, "errors": errors}
            if isinstance(envelope.get("observation_verification"), dict):
                invalid_result["observation_verification"] = envelope[
                    "observation_verification"
                ]
            invalid_results.append(invalid_result)
            continue
        observation_verification = envelope.get("observation_verification")
        if (
            not isinstance(observation_verification, dict)
            or observation_verification.get("verdict_sha256")
            != sha256_json(verdict)
            or bool(observation_verification.get("errors"))
        ):
            observation_verification = verify_verdict_observations(
                task,
                verdict,
                source_by_id.get(job.get("source_id")),
                target_by_id.get(job.get("target_id")),
                timeout=task.acceptance.build_timeout_seconds,
            )
        verification_records = observation_verification["records"]
        failed_chains = observation_verification["errors"]
        if failed_chains:
            invalid_results.append(
                {
                    "job_key": key,
                    "errors": failed_chains,
                    "observation_verification": observation_verification,
                }
            )
            continue
        valid_verdicts.append((job, verdict))
        match_status_counts[verdict["match_status"]] += 1
        alignment_counts[verdict["alignment"]] += 1
        if verdict.get("target_disposition"):
            target_dispositions[verdict["target_disposition"]] += 1
        failure_categories.update(verdict["failure_categories"])
        for verification_record in verification_records:
            kind = verification_record["kind"]
            observation = verification_record["observation"]
            verification = verification_record["verification"]
            record = {
                "job_key": key,
                "source_id": job.get("source_id"),
                "target_id": job.get("target_id"),
                "observation": observation,
                "verification": verification,
            }
            (examples if kind == "example" else counterexamples).append(record)

    source_count = source_index["declaration_count"]
    target_count = target_index["declaration_count"]
    match_only_target_count = sum(
        bool(item.get("match_only"))
        for item in target_index.get("declarations", [])
    )
    matched_target_ids = {
        item["target_id"] for item in plan["matching"]["matches"]
    }
    matched_match_only_target_count = sum(
        bool(item.get("match_only")) and item["id"] in matched_target_ids
        for item in target_index.get("declarations", [])
    )
    matched_count = len(plan["matching"]["matches"])
    aligned_count = alignment_counts["aligned"]
    not_aligned_count = alignment_counts["not_aligned"]
    uncertain_count = alignment_counts["uncertain"]
    planned_jobs = len(plan["jobs"])
    completed_jobs = len(valid_verdicts)
    compilation_passed = compile_result["status"] == "passed"
    # A repository-wide build is diagnostic, not an all-or-nothing semantic
    # gate.  Hierarchical judging separately gates every semantic module; flat
    # judging already rejects an item whose target harness cannot compile.
    known_failure = not_aligned_count > 0
    execution_complete = (
        completed_jobs == planned_jobs and not bool(invalid_results)
    )
    incomplete = (
        not execution_complete
        or not compilation_passed
        or bool(plan["matching"]["unmatched_source_ids"])
        or uncertain_count > 0
        or match_status_counts["wrong_match"] > 0
    )
    status = "failed" if known_failure else ("incomplete" if incomplete else "passed")
    decided = aligned_count + not_aligned_count
    verified_examples = sum(
        bool(item["verification"].get("chain_verified")) for item in examples
    )
    verified_counterexamples = sum(
        bool(item["verification"].get("chain_verified"))
        for item in counterexamples
    )
    return {
        "version": JUDGE_VERSION,
        "task_id": task.task_id,
        "status": status,
        "compile": compile_result,
        "inventory": {
            "source_declarations": source_count,
            "target_declarations": target_count,
            "match_only_target_candidates": match_only_target_count,
        },
        "matching": {
            "matched": matched_count,
            "matched_via_match_only_target": matched_match_only_target_count,
            "unmatched_source": len(plan["matching"]["unmatched_source_ids"]),
            "unmatched_target": len(plan["matching"]["unmatched_target_ids"]),
            "source_match_coverage": (
                matched_count / source_count if source_count else 1.0
            ),
        },
        "judging": {
            "planned_jobs": planned_jobs,
            "completed_valid_jobs": completed_jobs,
            "invalid_or_failed_jobs": invalid_results,
            "execution_status": (
                "complete" if execution_complete else "incomplete"
            ),
            "completion_rate": completed_jobs / planned_jobs if planned_jobs else 1.0,
            "match_status_counts": dict(sorted(match_status_counts.items())),
            "alignment_counts": dict(sorted(alignment_counts.items())),
            "alignment_rate_among_decided": (
                aligned_count / decided if decided else None
            ),
            "conservative_source_alignment_score": (
                aligned_count / source_count if source_count else 1.0
            ),
            "target_dispositions": dict(sorted(target_dispositions.items())),
        },
        "failure_clusters": dict(failure_categories.most_common()),
        "examples": examples,
        "example_summary": {
            "claimed": len(examples),
            "two_sided_chain_verified": verified_examples,
        },
        "counterexamples": counterexamples,
        "counterexample_summary": {
            "claimed": len(counterexamples),
            "two_sided_chain_verified": verified_counterexamples,
        },
        "unmatched": {
            "source_ids": plan["matching"]["unmatched_source_ids"],
            "target_ids": plan["matching"]["unmatched_target_ids"],
        },
        "reproducibility": {
            "source_index_sha256": plan["source_index_sha256"],
            "target_index_sha256": plan["target_index_sha256"],
            "judge_plan_sha256": sha256_json(plan),
            "prompt_version": plan["prompt_version"],
            "verdict_schema_sha256": sha256_json(VERDICT_SCHEMA),
        },
    }


def render_judge_report(report: dict[str, Any]) -> str:
    def inline(value: Any) -> str:
        rendered = normalize_space(str(value)).replace("`", "\\`")
        return f"`{rendered}`"

    def runtime_lines(
        observation: dict[str, Any], verification: dict[str, Any]
    ) -> list[str]:
        rendered: list[str] = []
        for side_name, label in (("source", "Source"), ("target", "Target")):
            side = observation[side_name]
            run = side["run"]
            verified_side = verification[side_name]
            command = (verified_side.get("result") or {}).get("command")
            rendered.extend(
                [
                    f"- {label} subject: {inline(side['subject'])}",
                    f"- {label} input expression: {inline(side['input']['expression'])}",
                    f"- {label} run: {inline(run['language'])}/{inline(run['mode'])}",
                    f"- {label} invocation: {inline(run['invocation'])}",
                    f"- {label} claimed output: {inline(side['output']['expression'])}",
                    f"- {label} observed output: {inline(verified_side.get('observed_output'))}",
                    f"- {label} compiler command: {inline(json.dumps(command, ensure_ascii=False))}",
                    f"- {label} chain verification: {inline(verified_side['status'])}",
                ]
            )
        return rendered

    inventory = report["inventory"]
    matching = report["matching"]
    judging = report["judging"]
    lines = [
        "# Semantic translation judge",
        "",
        f"- Decision: **{report['status'].upper()}**",
        f"- Target compilation: **{report['compile']['status'].upper()}**",
        (
            "- Judge execution: "
            f"**{judging.get('execution_status', 'incomplete').upper()}**"
        ),
        (
            f"- Source items matched: {matching['matched']}/"
            f"{inventory['source_declarations']} "
            f"({matching['source_match_coverage']:.1%})"
        ),
        (
            "- Match-only target projection candidates: "
            f"{inventory.get('match_only_target_candidates', 0)} "
            f"({matching.get('matched_via_match_only_target', 0)} matched)"
        ),
        (
            f"- Valid judge jobs: {judging['completed_valid_jobs']}/"
            f"{judging['planned_jobs']} ({judging['completion_rate']:.1%})"
        ),
        (
            "- Conservative source alignment score: "
            f"{judging['conservative_source_alignment_score']:.1%}"
        ),
        "",
        "## Outcome counts",
        "",
    ]
    for name, count in judging["alignment_counts"].items():
        lines.append(f"- `{name}`: {count}")
    if not judging["alignment_counts"]:
        lines.append("- No valid semantic verdicts yet.")
    lines.extend(["", "## Matching gaps", ""])
    lines.append(f"- Unmatched source items: {matching['unmatched_source']}")
    lines.append(f"- Unmatched target items: {matching['unmatched_target']}")
    lines.extend(["", "## Failure clusters", ""])
    if report["failure_clusters"]:
        for name, count in report["failure_clusters"].items():
            lines.append(f"- `{name}`: {count}")
    else:
        lines.append("- None reported.")
    lines.extend(["", "## Aligned examples", ""])
    if not report.get("examples"):
        lines.append("- None reported.")
    for index, item in enumerate(report.get("examples", []), start=1):
        observation = item["observation"]
        lines.extend(
            [
                f"### E{index}. `{item['source_id']}` → `{item['target_id']}`",
                "",
                f"- Observation ID: `{observation.get('id')}`",
                f"- Source input: {observation['source']['input']['description']}",
                f"- Source output: {observation['source']['output']['description']}",
                f"- Target input: {observation['target']['input']['description']}",
                f"- Target output: {observation['target']['output']['description']}",
                f"- Input alignment claim: `{observation['input_alignment']['status']}`",
                f"- Output alignment claim: `{observation['output_alignment']['status']}`",
            ]
        )
        lines.extend(runtime_lines(observation, item["verification"]))
        lines.append("")
    lines.extend(["", "## Counterexamples", ""])
    if not report["counterexamples"]:
        lines.append("- None reported.")
    for index, item in enumerate(report["counterexamples"], start=1):
        counterexample = item["observation"]
        lines.extend(
            [
                f"### {index}. `{item['source_id']}` → `{item['target_id']}`",
                "",
                f"- Observation ID: `{counterexample.get('id')}`",
                f"- Source input: {counterexample['source']['input']['description']}",
                f"- Source output: {counterexample['source']['output']['description']}",
                f"- Target input: {counterexample['target']['input']['description']}",
                f"- Target output: {counterexample['target']['output']['description']}",
                f"- Input alignment claim: `{counterexample['input_alignment']['status']}`",
                f"- Output alignment claim: `{counterexample['output_alignment']['status']}`",
            ]
        )
        lines.extend(runtime_lines(counterexample, item["verification"]))
        lines.append("")
    if judging["invalid_or_failed_jobs"]:
        lines.extend(["", "## Invalid or failed judge jobs", ""])
        for item in judging["invalid_or_failed_jobs"]:
            lines.append(
                f"- `{item['job_key']}`: "
                + "; ".join(item.get("errors") or ["unknown failure"])
            )
        lines.append("")
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            "Compilation and semantic alignment are separate gates. Every scored aligned "
            "example and not-aligned counterexample has a verified source and target "
            "input-to-output chain. Cross-language input/output alignment and the final "
            "generalization from aligned examples remain semantic judge claims. Missing, "
            "rejected, unavailable, unverified, or contradicted chains invalidate the verdict rather "
            "than contributing to alignment counts.",
            "",
        ]
    )
    return "\n".join(lines)
