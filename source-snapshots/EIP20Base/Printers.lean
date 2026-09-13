import EIP20Base.Token

namespace EIP20Base

variable {α κ ν : Type}

class Show (α : Type) where
  render : α → String

def showValue [Show α] (value : α) : String := Show.render value
def sep : String := ", "

instance showNat : Show Nat := ⟨toString⟩
instance showInt : Show Int := ⟨toString⟩
instance showAddress [ChainBase] : Show Address := ⟨reprStr⟩

instance showOption [Show α] : Show (Option α) where
  render
    | none => "None"
    | some value => "Some " ++ showValue value

instance showList [Show α] : Show (List α) := ⟨fun xs =>
  "[" ++ String.intercalate "; " (xs.map showValue) ++ "]"⟩

def showMap [LinearOrder κ] [Show κ] [Show ν] (map : FMap κ ν) : String :=
  "{" ++ String.intercalate "; " ((FMap.elements map).map fun (k, v) =>
    showValue k ++ " ↦ " ++ showValue v) ++ "}"

namespace EIP20Token

variable [ChainBase]

instance showTokenValue : Show TokenValue := ⟨toString⟩

instance showMsg : Show Msg where
  render
    | .transfer recipient amount => "transfer " ++ showValue recipient ++ " " ++ showValue amount
    | .transfer_from ownerAddr recipient amount =>
        "transfer_from " ++ showValue ownerAddr ++ " " ++ showValue recipient ++ " " ++ showValue amount
    | .approve delegate amount => "approve " ++ showValue delegate ++ " " ++ showValue amount

instance showTokenSetup : Show Setup := ⟨fun setup =>
  "Setup{owner: " ++ showValue setup.owner ++ sep ++
  "init_amount: " ++ showValue setup.init_amount ++ "}"⟩

instance showAllowanceMap : Show (FMap Address TokenValue) := ⟨showMap⟩

instance showTokenState : Show State := ⟨fun state =>
  "State{total_supply: " ++ showValue state.total_supply ++ sep ++
  "balances: " ++ showMap state.balances ++ sep ++
  "allowances: " ++ showMap state.allowances ++ "}"⟩

inductive SerializedValue where
  | msg (value : Msg)
  | setup (value : Setup)

instance showSerializedMsg : Show SerializedValue where
  render
    | .msg value => showValue value
    | .setup value => showValue value

end EIP20Token
end EIP20Base
