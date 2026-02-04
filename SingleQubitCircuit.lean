import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.CPTPMap  -- brings in 𝐔

/-- Primitive single-qubit gates, as syntax. -/
inductive SingleQubitGate
  | Z | X | Y | H | S | T
deriving Repr, DecidableEq

/-- A single-qubit circuit is a list of gates applied in order (head first). -/
abbrev SingleQubitCircuit := List SingleQubitGate

namespace SingleQubitGate

/-- Interpret a primitive gate as the corresponding unitary 𝐔[Qubit]. -/
noncomputable def toUnitary : SingleQubitGate → 𝐔[Qubit]
  | .Z => Qubit.Z
  | .X => Qubit.X
  | .Y => Qubit.Y
  | .H => Qubit.H
  | .S => Qubit.S
  | .T => Qubit.T

end SingleQubitGate

/-- Evaluate a circuit to a single unitary, left-to-right application. -/
noncomputable def evalCircuit (c : SingleQubitCircuit) : 𝐔[Qubit] :=
  c.foldl (fun U g => SingleQubitGate.toUnitary g * U) (1 : 𝐔[Qubit])

/-- Boolean check: do two circuits have exactly the same 2×2 unitary matrix? -/
noncomputable def circuitsEqBool (c₁ c₂ : SingleQubitCircuit) : Bool :=
  let U₁ := (evalCircuit c₁).val
  let U₂ := (evalCircuit c₂).val
  let e00 := decide (U₁ 0 0 = U₂ 0 0)
  let e01 := decide (U₁ 0 1 = U₂ 0 1)
  let e10 := decide (U₁ 1 0 = U₂ 1 0)
  let e11 := decide (U₁ 1 1 = U₂ 1 1)
  e00 && e01 && e10 && e11

-- Examples: use circuitsEqBool directly with literal circuits
lemma hh_id_eq: circuitsEqBool [.H, .H] [] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp

lemma ss_z_eq : circuitsEqBool [.S, .S] [.Z] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp [Qubit.S_sq]

lemma hh_xx_eq : circuitsEqBool [.H, .H] [.X, .X] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp [Qubit.H_sq, Qubit.X_sq]

lemma hhh_h_eq : circuitsEqBool [.H, .H, .H] [.H] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp

lemma xxx_x_eq : circuitsEqBool [.X, .X, .X] [.X] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp

lemma xxxx_id_eq : circuitsEqBool [.X, .X, .X, .X] [.X, .X, .Z, .Z] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp

lemma ssz_zz_eq : circuitsEqBool [.S, .S, .Z] [.Z, .Z] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp [Qubit.Z_sq]

lemma test : circuitsEqBool [.X, .X, .X] [.H, .H, .X] = true := by
  unfold circuitsEqBool evalCircuit SingleQubitGate.toUnitary
  simp
