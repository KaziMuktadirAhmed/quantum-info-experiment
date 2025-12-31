import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.CPTPMap
import SingleQubitCircuit

/-- A two-qubit gate type encompassing both single-qubit gates on specific wires
    and native two-qubit gates -/
inductive TwoQubitGate where
  | single (wire : Fin 2) (g : SingleQubitGate)
  | cnot
  | swap
  | cz
deriving Repr, DecidableEq

abbrev TwoQubitCircuit := List TwoQubitGate

namespace TwoQubitGate

/-- Pretty printing for two-qubit gates -/
def toString : TwoQubitGate → String
  | .single 0 g => s!"q[0]: {repr g}"
  | .single 1 g => s!"q[1]: {repr g}"
  | .cnot => "CNOT(0→1)"
  | .swap => "SWAP(0,1)"
  | .cz => "CZ(0,1)"

instance : ToString TwoQubitGate where
  toString := TwoQubitGate.toString

end TwoQubitGate

namespace TwoQubitCircuit

/-- Pretty print a two-qubit circuit -/
def toString (c : TwoQubitCircuit) : String :=
  s!"[{String.intercalate ", " (c.map TwoQubitGate.toString)}]"

instance : ToString TwoQubitCircuit where
  toString := TwoQubitCircuit.toString

end TwoQubitCircuit

-- (TwoQubitGate and TwoQubitCircuit definitions here)

namespace TwoQubitGate

open Matrix

/-- Lift a single-qubit gate to act on wire 0 (tensor with identity on wire 1) -/
noncomputable def liftToWire0 (U : 𝐔[Qubit]) : 𝐔[Qubit × Qubit] :=
  U ⊗ᵤ (1 : 𝐔[Qubit])

/-- Lift a single-qubit gate to act on wire 1 (identity on wire 0, gate on wire 1) -/
noncomputable def liftToWire1 (U : 𝐔[Qubit]) : 𝐔[Qubit × Qubit] :=
  (1 : 𝐔[Qubit]) ⊗ᵤ U

/-- Convert a TwoQubitGate to its 4×4 unitary matrix -/
noncomputable def toUnitary : TwoQubitGate → 𝐔[Qubit × Qubit]
  | .single wire g =>
      match wire with
      | 0 => liftToWire0 (SingleQubitGate.toUnitary g)
      | 1 => liftToWire1 (SingleQubitGate.toUnitary g)
  | .cnot => Qubit.CNOT
  | .swap => ⟨Matrix.of fun (i₁, j₁) (i₂, j₂) =>
      if (i₁, j₁) = (i₂, j₂) then 1
      else if (i₁, j₁) = (j₂, i₂) then 1
      else 0, by sorry⟩
  | .cz => Qubit.controllize Qubit.Z

end TwoQubitGate

namespace TwoQubitCircuit

/-- Evaluate a two-qubit circuit to its 4×4 unitary matrix -/
noncomputable def evalCircuit (c : TwoQubitCircuit) : 𝐔[Qubit × Qubit] :=
  c.foldl (fun U g => TwoQubitGate.toUnitary g * U) (1 : 𝐔[Qubit × Qubit])

end TwoQubitCircuit

-- Example: CNOT twice equals identity
example : TwoQubitCircuit.evalCircuit [.cnot, .cnot] = (1 : 𝐔[Qubit × Qubit]) := by
  sorry

-- Example: H on wire 0, then H on wire 0 equals identity on that wire
example : TwoQubitCircuit.evalCircuit [.single 0 .H, .single 0 .H] = (1 : 𝐔[Qubit × Qubit]) := by
  sorry
