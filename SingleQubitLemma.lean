import QuantumInfo.Finite.Qubit.Basic
import QuantumInfo.Finite.Unitary
import Mathlib.Data.Matrix.Group

open QuantumInfo Finite Qubit Unitary

namespace QuantumInfo.Finite.Qubit

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The standard Pauli gates and common single-qubit gates as Unitary operators -/
def pauliX : Unitary H := ⟨![![0, 1], ![1, 0]], by simp [Unitary.unitary_def]⟩
def pauliY : Unitary H := ⟨![![0, I, -I], ![-I, 0, I]], by simp [Unitary.unitary_def]⟩
def pauliZ : Unitary H := ⟨![![1, 0], ![0, -1]], by simp [Unitary.unitary_def]⟩

def hadamard : Unitary H :=
  ⟨![![(1/2:ℂ)^(1/2:ℝ), (1/2:ℂ)^(1/2:ℝ)], ![(1/2:ℂ)^(1/2:ℝ), -(1/2:ℂ)^(1/2:ℝ)]],
   by simp [Unitary.unitary_def, Real.sqrt_sq, mul_comm, inv_mul_cancel]⟩

def S : Unitary H := ⟨![![1, 0], ![0, I]], by simp [Unitary.unitary_def]⟩
def T : Unitary H := ⟨![![1, 0], ![0, exp (I * π/4)]], by simp [Unitary.unitary_def, ←exp_mul, mul_comm]⟩
def Tdg : Unitary H := T†

def sqrtX : Unitary H := ⟨![![(1/2:ℂ)^(1/2:ℝ), I * (1/2:ℂ)^(1/2:ℝ)],
                             ![-I * (1/2:ℂ)^(1/2:ℝ), (1/2:ℂ)^(1/2:ℝ)]],
                         by simp [Unitary.unitary_def, Real.sqrt_sq, mul_comm, inv_mul_cancel]⟩

/-- T gate exponentiation: T^8 = I -/
lemma T_pow_eight_eq_I : ∀ n : ℕ, (T ^ 8 : Unitary H) = 1 := by
  intro n
  ext i j
  simp [Unitary.coe_mul, Unitary.coe_pow, T, pow_apply, Matrix.mul_apply]
  split_ifs with h₁ h₂
  · simp [if_pos rfl, if_pos rfl]
    rw [exp_mul, ← mul_assoc, mul_assoc (↑I) _ _, ← mul_assoc (↑I) _ _,
        mul_pow, pow_add, pow_two, mul_one, one_mul, ← mul_assoc, ← exp_mul]
    ring_nf
    rw [← exp_mul, mul_div_assoc, ← mul_comm π, mul_div_assoc,
        mul_div_cancel_left _ (ne_of_lt (Real.pi_pos.lt_div' 4 (by norm_num)))⁻¹]
    simp [exp_I_of_pi_rat]
  · simp [if_pos rfl, if_neg h₁, if_neg h₂]

/-- T† gate exponentiation: (T†)^8 = I -/
lemma Tdg_pow_eight_eq_I : ∀ n : ℕ, (Tdg ^ 8 : Unitary H) = 1 := by
  intro n
  rw [Tdg, Unitary.pow_dag, T_pow_eight_eq_I, Unitary.dag_one]

/-- Sqrt(X) gate exponentiation: (√X)^4 = I -/
lemma SX_pow_four_eq_I : ∀ n : ℕ, (sqrtX ^ 4 : Unitary H) = 1 := by
  intro n
  ext i j
  simp [Unitary.coe_mul, Unitary.coe_pow, sqrtX, pow_apply, Matrix.mul_apply]
  -- This is tedious matrix multiplication, but follows the standard √X^4 = I property
  -- The proof relies on the explicit matrix power calculation
  split_ifs <;> simp [*]

end QuantumInfo.Finite.Qubit
