import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.CPTPMap
import SingleQubitCircuit

-- ============================================================
-- FIX: CPTPMap imports its own ⊗ᵤ notation which shadows
-- Matrix.unitary_kron. We re-pin it here with a local notation
-- so every ⊗ᵤ in this file unambiguously means unitary_kron.
-- ============================================================
local notation:60 a " ⊗ᵤ " b => Matrix.unitary_kron a b

open Matrix BigOperators
open Matrix.Kronecker  -- brings in ⊗ₖ (kroneckerMap) and mul_kronecker_mul

-- ============================================================
-- SECTION 1: SHARED HELPER LEMMAS
-- Core @[simp] lemmas needed by all circuit equivalence proofs.
-- ============================================================

/-- The underlying matrix of a unitary Kronecker product equals
    the Kronecker product of the underlying matrices. Proved by rfl. -/
@[simp]
lemma unitary_kron_val {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (a : 𝐔[α]) (b : 𝐔[β]) :
    (Matrix.unitary_kron a b).val = a.val ⊗ₖ b.val := rfl

/-- The identity unitary has the identity matrix as its value. -/
@[simp]
lemma unitary_one_val {α : Type*} [Fintype α] [DecidableEq α] :
    (1 : 𝐔[α]).val = (1 : Matrix α α ℂ) := rfl

/-- Multiplication of unitary subtype values is the underlying matrix product. -/
@[simp]
lemma unitary_mul_val {α : Type*} [Fintype α] [DecidableEq α]
    (a b : 𝐔[α]) :
    (a * b).val = a.val * b.val := rfl

-- ============================================================
-- SECTION 2: TWO-QUBIT CIRCUIT
-- Space: Qubit × Qubit (4×4 unitaries)
-- ============================================================

inductive TwoQubitGate where
  | single (wire : Fin 2) (g : SingleQubitGate)
  | cnot   -- CNOT: control=0, target=1
  | cz     -- Controlled-Z
deriving Repr, DecidableEq

abbrev TwoQubitCircuit := List TwoQubitGate

namespace TwoQubitGate
open Qubit

/-- Lift 1-qubit gate to wire 0: U ⊗ I -/
noncomputable def liftWire0 (U : 𝐔[Qubit]) : 𝐔[Qubit × Qubit] :=
  Matrix.unitary_kron U (1 : 𝐔[Qubit])

/-- Lift 1-qubit gate to wire 1: I ⊗ U -/
noncomputable def liftWire1 (U : 𝐔[Qubit]) : 𝐔[Qubit × Qubit] :=
  Matrix.unitary_kron (1 : 𝐔[Qubit]) U

noncomputable def toUnitary : TwoQubitGate → 𝐔[Qubit × Qubit]
  | .single 0 g => liftWire0 (SingleQubitGate.toUnitary g)
  | .single 1 g => liftWire1 (SingleQubitGate.toUnitary g)
  | .single _ _ => 1  -- unreachable for Fin 2; needed for totality
  | .cnot       => Qubit.CNOT
  | .cz         => Qubit.controllize Qubit.Z

end TwoQubitGate

namespace TwoQubitCircuit

/-- Evaluate a 2-qubit circuit left-to-right into a single unitary. -/
noncomputable def evalCircuit (c : TwoQubitCircuit) : 𝐔[Qubit × Qubit] :=
  c.foldl (fun U g => TwoQubitGate.toUnitary g * U) (1 : 𝐔[Qubit × Qubit])

/-- Two 2-qubit circuits are equivalent iff their unitary matrices are equal. -/
def circuitsEq (c₁ c₂ : TwoQubitCircuit) : Prop :=
  (evalCircuit c₁).val = (evalCircuit c₂).val

-- ────────────────────────────────────────────────────────────
-- 2-QUBIT BENCHMARKS
-- Each lemma is wrapped in #count_heartbeats.
-- The output line "Used N heartbeats" is your benchmark result.
-- Increase maxHeartbeats if Lean times out before proving.
-- ────────────────────────────────────────────────────────────

-- BENCHMARK 2Q-1: CNOT · CNOT = I
set_option maxHeartbeats 400000 in
#count_heartbeats in
lemma cnot_twice_is_id : circuitsEq [.cnot, .cnot] [] := by
  simp [circuitsEq, evalCircuit,
        TwoQubitGate.toUnitary, TwoQubitGate.liftWire0, TwoQubitGate.liftWire1,
        unitary_kron_val, unitary_one_val, unitary_mul_val,
        Matrix.mul_kronecker_mul,
        Qubit.CNOT, Qubit.controllize_mul, Qubit.X_sq]

-- BENCHMARK 2Q-2: CZ · CZ = I
set_option maxHeartbeats 400000 in
#count_heartbeats in
lemma cz_twice_is_id : circuitsEq [.cz, .cz] [] := by
  simp [circuitsEq, evalCircuit,
        TwoQubitGate.toUnitary, TwoQubitGate.liftWire0, TwoQubitGate.liftWire1,
        unitary_kron_val, unitary_one_val, unitary_mul_val,
        Matrix.mul_kronecker_mul,
        Qubit.controllize, Qubit.controllize_mul, Qubit.Z_sq]

end TwoQubitCircuit

-- ============================================================
-- SECTION 3: THREE-QUBIT CIRCUIT
-- Space: Qubit × (Qubit × Qubit) (8×8 unitaries)
-- Wire layout: wire 0 = left qubit, wire 2 = rightmost qubit
-- ============================================================

inductive ThreeQubitGate where
  | single (wire : Fin 3) (g : SingleQubitGate)
  | cnot01  -- CNOT: control=0, target=1
  | cnot12  -- CNOT: control=1, target=2
deriving Repr, DecidableEq

abbrev ThreeQubitCircuit := List ThreeQubitGate

namespace ThreeQubitGate
open Qubit

/-- Lift 1-qubit gate to wire 0: U ⊗ I₂ ⊗ I₂ = U ⊗ I₄ -/
noncomputable def liftWire0 (U : 𝐔[Qubit]) : 𝐔[Qubit × (Qubit × Qubit)] :=
  Matrix.unitary_kron U (1 : 𝐔[Qubit × Qubit])

/-- Lift 1-qubit gate to wire 1: I₂ ⊗ U ⊗ I₂ -/
noncomputable def liftWire1 (U : 𝐔[Qubit]) : 𝐔[Qubit × (Qubit × Qubit)] :=
  Matrix.unitary_kron (1 : 𝐔[Qubit]) (Matrix.unitary_kron U (1 : 𝐔[Qubit]))

/-- Lift 1-qubit gate to wire 2: I₄ ⊗ U -/
noncomputable def liftWire2 (U : 𝐔[Qubit]) : 𝐔[Qubit × (Qubit × Qubit)] :=
  Matrix.unitary_kron (1 : 𝐔[Qubit × Qubit]) U

/-- Lift 2-qubit gate onto wires 0–1: G ⊗ I₂ -/
noncomputable def liftTo01 (G : 𝐔[Qubit × Qubit]) : 𝐔[Qubit × (Qubit × Qubit)] :=
  Matrix.unitary_kron G (1 : 𝐔[Qubit])

/-- Lift 2-qubit gate onto wires 1–2: I₂ ⊗ G -/
noncomputable def liftTo12 (G : 𝐔[Qubit × Qubit]) : 𝐔[Qubit × (Qubit × Qubit)] :=
  Matrix.unitary_kron (1 : 𝐔[Qubit]) G

noncomputable def toUnitary : ThreeQubitGate → 𝐔[Qubit × (Qubit × Qubit)]
  | .single 0 g => liftWire0 (SingleQubitGate.toUnitary g)
  | .single 1 g => liftWire1 (SingleQubitGate.toUnitary g)
  | .single 2 g => liftWire2 (SingleQubitGate.toUnitary g)
  | .single _ _ => 1  -- unreachable for Fin 3
  | .cnot01     => liftTo01 Qubit.CNOT
  | .cnot12     => liftTo12 Qubit.CNOT

end ThreeQubitGate

namespace ThreeQubitCircuit

/-- Evaluate a 3-qubit circuit left-to-right into a single unitary. -/
noncomputable def evalCircuit (c : ThreeQubitCircuit) : 𝐔[Qubit × (Qubit × Qubit)] :=
  c.foldl (fun U g => ThreeQubitGate.toUnitary g * U) (1 : 𝐔[Qubit × (Qubit × Qubit)])

/-- Two 3-qubit circuits are equivalent iff their unitary matrices are equal. -/
def circuitsEq (c₁ c₂ : ThreeQubitCircuit) : Prop :=
  (evalCircuit c₁).val = (evalCircuit c₂).val

-- Shared simp set for all 3-qubit proofs
private def threeQubitSimp := [
  @ThreeQubitCircuit.circuitsEq, @ThreeQubitCircuit.evalCircuit,
  @ThreeQubitGate.toUnitary,
  @ThreeQubitGate.liftTo01, @ThreeQubitGate.liftTo12,
  @ThreeQubitGate.liftWire0, @ThreeQubitGate.liftWire1, @ThreeQubitGate.liftWire2,
  @unitary_kron_val, @unitary_one_val, @unitary_mul_val,
  @Matrix.mul_kronecker_mul,
  @Qubit.CNOT, @Qubit.controllize_mul, @Qubit.X_sq
]

-- ────────────────────────────────────────────────────────────
-- 3-QUBIT BENCHMARKS
-- ────────────────────────────────────────────────────────────

-- BENCHMARK 3Q-1: CNOT01 · CNOT01 = I
set_option maxHeartbeats 800000 in
#count_heartbeats in
lemma cnot01_twice_is_id : circuitsEq [.cnot01, .cnot01] [] := by
  simp [circuitsEq, evalCircuit,
        ThreeQubitGate.toUnitary,
        ThreeQubitGate.liftTo01, ThreeQubitGate.liftTo12,
        ThreeQubitGate.liftWire0, ThreeQubitGate.liftWire1, ThreeQubitGate.liftWire2,
        unitary_kron_val, unitary_one_val, unitary_mul_val,
        Matrix.mul_kronecker_mul,
        Qubit.CNOT, Qubit.controllize_mul, Qubit.X_sq]

-- BENCHMARK 3Q-2: CNOT12 · CNOT12 = I
set_option maxHeartbeats 800000 in
#count_heartbeats in
lemma cnot12_twice_is_id : circuitsEq [.cnot12, .cnot12] [] := by
  simp [circuitsEq, evalCircuit,
        ThreeQubitGate.toUnitary,
        ThreeQubitGate.liftTo01, ThreeQubitGate.liftTo12,
        ThreeQubitGate.liftWire0, ThreeQubitGate.liftWire1, ThreeQubitGate.liftWire2,
        unitary_kron_val, unitary_one_val, unitary_mul_val,
        Matrix.mul_kronecker_mul,
        Qubit.CNOT, Qubit.controllize_mul, Qubit.X_sq]

-- BENCHMARK 3Q-3: CNOT01·CNOT12·CNOT01 = CNOT12·CNOT01·CNOT12
-- (both implement SWAP on wires 0–2 in adjacent-CNOT encoding)
set_option maxHeartbeats 1600000 in
#count_heartbeats in
lemma swap_via_cnots :
    circuitsEq [.cnot01, .cnot12, .cnot01] [.cnot12, .cnot01, .cnot12] := by
  simp [circuitsEq, evalCircuit,
        ThreeQubitGate.toUnitary,
        ThreeQubitGate.liftTo01, ThreeQubitGate.liftTo12,
        ThreeQubitGate.liftWire0, ThreeQubitGate.liftWire1, ThreeQubitGate.liftWire2,
        unitary_kron_val, unitary_one_val, unitary_mul_val,
        Matrix.mul_kronecker_mul,
        Qubit.CNOT, Qubit.controllize_mul, Qubit.X_sq]

end ThreeQubitCircuit

-- ============================================================
-- SECTION 4: HOW TO ADD YOUR OWN BENCHMARK
-- ============================================================
--
-- For a 3-qubit circuit pair, use this template:
--
--   set_option maxHeartbeats <N> in
--   #count_heartbeats in
--   lemma my_benchmark_name :
--       ThreeQubitCircuit.circuitsEq
--         [.cnot01, .cnot12, ...]   -- circuit 1
--         [.cnot12, .cnot01, ...] := by  -- circuit 2
--     simp [ThreeQubitCircuit.circuitsEq,
--           ThreeQubitCircuit.evalCircuit,
--           ThreeQubitGate.toUnitary,
--           ThreeQubitGate.liftTo01, ThreeQubitGate.liftTo12,
--           ThreeQubitGate.liftWire0, ThreeQubitGate.liftWire1, ThreeQubitGate.liftWire2,
--           unitary_kron_val, unitary_one_val, unitary_mul_val,
--           Matrix.mul_kronecker_mul,
--           Qubit.CNOT, Qubit.controllize_mul, Qubit.X_sq, Qubit.Z_sq,
--           Qubit.H_sq, Qubit.S_sq]
--
-- Tips:
--   • Start with maxHeartbeats 400000 for 2-qubit, 800000 for 3-qubit.
--   • The "Used N heartbeats" line in the InfoView is your measurement.
--   • More gates in the circuit = more heartbeats needed.
--   • If simp loops, add `set_option maxRecDepth 1000` above the lemma.
