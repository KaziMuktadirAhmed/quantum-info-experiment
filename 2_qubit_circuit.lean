import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.CPTPMap
import SingleQubitCircuit

set_option diagnostics true
set_option maxHeartbeats 1000000

inductive TwoQubitGate where
  | single (wire : Fin 2) (g : SingleQubitGate)
  | cnot
  | swap
  | cz
deriving Repr, DecidableEq

abbrev TwoQubitCircuit := List TwoQubitGate
namespace TwoQubitGate
open Matrix

def toString : TwoQubitGate → String
  | .single 0 g => s!"q[0]: {repr g}"
  | .single 1 g => s!"q[1]: {repr g}"
  | .cnot => "CNOT(0→1)"
  | .swap => "SWAP(0,1)"
  | .cz => "CZ(0,1)"
instance : ToString TwoQubitGate where toString := toString

/-- Lift single-qubit gate to wire 0 (U ⊗ I) -/
noncomputable def liftToWire0 (U : 𝐔[Qubit]) : 𝐔[Qubit × Qubit] := U ⊗ᵤ (1 : 𝐔[Qubit])

/-- Lift single-qubit gate to wire 1 (I ⊗ U) -/
noncomputable def liftToWire1 (U : 𝐔[Qubit]) : 𝐔[Qubit × Qubit] := (1 : 𝐔[Qubit]) ⊗ᵤ U

/-- Convert gate to 4×4 unitary matrix -/
noncomputable def toUnitary : TwoQubitGate → 𝐔[Qubit × Qubit]
  | .single wire g => match wire with
    | 0 => liftToWire0 (SingleQubitGate.toUnitary g)
    | 1 => liftToWire1 (SingleQubitGate.toUnitary g)
  | .cnot => Qubit.CNOT
  | .swap => ⟨Matrix.of fun (i₁, j₁) (i₂, j₂) =>
      if (i₁, j₁) = (i₂, j₂) then 1 else if (i₁, j₁) = (j₂, i₂) then 1 else 0, by sorry⟩
  | .cz => Qubit.controllize Qubit.Z
end TwoQubitGate

namespace TwoQubitCircuit

def toString (c : TwoQubitCircuit) : String :=
  s!"[{String.intercalate ", " (c.map TwoQubitGate.toString)}]"
instance : ToString TwoQubitCircuit where toString := toString

noncomputable def evalCircuit (c : TwoQubitCircuit) : 𝐔[Qubit × Qubit] :=
  c.foldl (fun U g => TwoQubitGate.toUnitary g * U) (1 : 𝐔[Qubit × Qubit])

/-- All 2-qubit basis states -/
def basisStates : List (Qubit × Qubit) := [(0,0), (0,1), (1,0), (1,1)]

/-- Check if two circuits have identical unitaries (all 16 matrix entries equal) -/
noncomputable def circuitsEqBool (c₁ c₂ : TwoQubitCircuit) : Bool :=
  let U₁ := (evalCircuit c₁).val
  let U₂ := (evalCircuit c₂).val
  (basisStates.product basisStates).all fun (row, col) =>
    decide (U₁ row col = U₂ row col)

lemma TwiceId : circuitsEqBool [.cnot, .cnot] [] = true := by
  unfold circuitsEqBool evalCircuit TwoQubitGate.toUnitary
  simp [basisStates]
  all_goals
  {
    simp [Matrix.mul_apply, Qubit.CNOT, Qubit.X]
    ring  -- This handles the ∑ sums automatically!
  }

end TwoQubitCircuit
