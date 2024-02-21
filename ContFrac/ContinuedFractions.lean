/-
Following the exposition from https://arxiv.org/pdf/math/0601660.pdf
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Tactic
import Mathlib.Analysis.Convolution

/-
Step 1: continued fractions
-/
def ContFrac := ℕ → ℕ

--i-th convergent, as a list
def list_of_CF (a : ContFrac) : ℕ → List ℚ
  | 0 => [a 0]
  | (n+1) => (list_of_CF a n) ++ [(a (n+1) : ℚ)]

--from a finite continued fraction to a rational
def conv_of_list : List ℚ → ℚ
| [] => 0
| [n] => n
| (n :: l) => n + 1/(conv_of_list l)

@[simp]
lemma conv_of_list_singleton (n : ℚ) : conv_of_list [n] = n := rfl
@[simp]
lemma conv_of_list_cons (n : ℚ) (l : List ℚ) : conv_of_list (n :: l) = n + 1/(conv_of_list l) := by
  cases' l
  simp; rfl; rfl

lemma conv_concat (l : List ℚ) (n₁ n₂ : ℚ) : conv_of_list (l ++ [n₁, n₂]) = conv_of_list (l ++ [n₁ + 1/n₂]) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [conv_of_list, ih]

section basics

variable (a : ContFrac) (i : ℕ)

def conv : ℚ := conv_of_list (list_of_CF a i)

def p (a : ContFrac) : ℕ → ℕ
| 0 => a 0
| 1 => (a 0)*(a 1) + 1
| (n + 2) => (a (n + 2))*(p a (n + 1)) + p a n

def q (a : ContFrac) : ℕ → ℕ
| 0 => 1
| 1 => a 1
| (n + 2) => (a (n + 2))*(q a (n + 1)) + q a n

lemma conv_rec_p : p a (i+2) = (a (i+2))*(p a (i+1)) + p a (i) := rfl
lemma conv_rec_q : q a (i+2) = (a (i+2))*(q a (i+1)) + q a (i) := rfl

lemma p_zero : p a 0 = a 0 := rfl
lemma p_one : p a 1 = (a 0)*(a 1) + 1 := rfl

lemma q_zero : q a 0 = 1 := rfl
lemma q_one : q a 1 = a 1 := rfl

end basics

lemma conv_eq_p_div_q (i : ℕ) : ∀ (a : ContFrac), a i ≠ 0 → conv a i = (p a i : ℚ) / q a i := by
  --strong induction on i
  induction' i using Nat.strong_induction_on with i ih
  intro a hi
  cases' i with i
  --case i = 0
  . simp [p, q]; rfl
  cases' i with i
  --case i = 1
  . simp [p, q]
    show (a 0 : ℚ) + 1/(a 1) = _
    field_simp
  have H : a (i + 1) + (1 : ℚ)/a (i + 2) ≠ 0 → conv a (i + 2) = p a (i + 2)/ q a (i + 2)
  . intro h
    rw [conv, list_of_CF, list_of_CF]
    sorry
  by_cases H1 : a (i + 1) = 0
  by_cases H0 : a i = 0
  --case [..., 0,0, a_{i+2}]
  . have Hp : p a (i + 2) = p a i
    . sorry
    have Hq : q a (i + 2) = q a i
    . sorry
    rw [Hp, Hq]
    sorry
  --case [..., a_i, 0, a_{i+2}]
  . apply H
    simp [H1, hi]
  --case [..., a_{i-1}, a_{i+2}]
  . apply H
    field_simp
    norm_cast
    simp [H1]


--TODO: define the sequence [1,0,1,1,2,1,1,4,1,1,6,1,...] for e
def e_seq : ContFrac := λ x => if x % 3 = 1 then 2*(x-1)/3 else 1
def P := p e_seq
def Q := q e_seq
noncomputable def e := Real.exp 1


@[simp]
lemma e_seq_0_mod_3 (n : ℕ) : e_seq (3*n) = 1 := by simp [e_seq]
@[simp]
lemma e_seq_1_mod_3 (n : ℕ) : e_seq (3*n + 1) = 2*n := by
  have H : (3*n + 1) % 3 = 1 := by simp [Nat.add_mod]
  simp [e_seq, H]
  rw [mul_comm 3, ←mul_assoc, Nat.mul_div_cancel]
  norm_num
@[simp]
lemma e_seq_2_mod_3 (n : ℕ) : e_seq (3*n + 2) = 1 := by
  have H : (3*n + 2) % 3 = 2 := by simp [Nat.add_mod]
  simp [e_seq, H]


--have a bunch of recurrence relations for the p_i and q_i
lemma P0 (n : ℕ) : P (3*n+3) = P (3*n + 2) + P (3*n + 1) := by
  rw[P, conv_rec_p]
  have H : 3*n + 1 + 2 = 3*(n + 1) := by simp [mul_add]
  simp [H]

lemma P1 (n : ℕ) : P (3*n+4) = (2*(n+1))*(P (3*n + 3)) + P (3*n + 2) := by
  have H : 3*n + 4 = 3*(n + 1) + 1 := by simp[mul_add]
  have H₁ : P (3*n + 4) = e_seq (3*n + 4)* P (3*n + 3) + P (3*n + 2) := by rw [P, conv_rec_p]
  convert H₁ using 3
  rw [H, e_seq_1_mod_3]

lemma P2 (n : ℕ) : P (3*n+2) = P (3*n + 1) + P (3*n) := by
  rw[P, conv_rec_p]
  have H : 3*n + 1 + 2 = 3*(n + 1) := by simp [mul_add]
  simp [H]

lemma Q0 (n : ℕ) : Q (3*n+3) = Q (3*n + 2) + Q (3*n + 1) := by
  rw[Q, conv_rec_q]
  have H : 3*n + 1 + 2 = 3*(n + 1) := by simp [mul_add]
  simp [H]

lemma Q1 (n : ℕ) : Q (3*n+4) = (2*(n+1))*(Q (3*n + 3)) + Q (3*n + 2) := by
  have H : 3*n + 4 = 3*(n + 1) + 1 := by simp[mul_add]
  have H₁ : Q (3*n + 4) = e_seq (3*n + 4)* Q (3*n + 3) + Q (3*n + 2) := by rw [Q, conv_rec_q]
  convert H₁ using 3
  rw [H, e_seq_1_mod_3]

lemma Q2 (n : ℕ) : Q (3*n+2) = Q (3*n + 1) + Q (3*n) := by
  rw[Q, conv_rec_q]
  have H : 3*n + 1 + 2 = 3*(n + 1) := by simp [mul_add]
  simp [H]

/-
Step 2: integrals
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)
open intervalIntegral Real

--just some examples
example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example (a b : ℝ) : (∫ x in a..b, exp x) = exp b - exp a := integral_exp

#check integral_mul_deriv_eq_deriv_mul

theorem integration_by_parts_left (a b : ℝ) : (∫ x in a..b, x*(exp x)) = (b*(exp b) - exp b) - (a*(exp a) - exp a) := by
  rw [integral_mul_deriv_eq_deriv_mul (v := exp) (u' := 1)]
  simp [one_mul]
  ring
  . exact fun x _ => hasDerivAt_id' x
  . exact fun x _ => hasDerivAt_exp x
  . apply Continuous.intervalIntegrable
    exact continuous_one
  . apply Continuous.intervalIntegrable
    exact continuous_exp

--magical integrals
noncomputable def A (n : ℕ) := ∫ x in (0 : ℝ)..1, x^n*(x-1)^n/n.factorial * (exp x)
noncomputable def B (n : ℕ) := ∫ x in (0 : ℝ)..1, x^(n+1)*(x-1)^n/n.factorial * (exp x)
noncomputable def C (n : ℕ) := ∫ x in (0 : ℝ)..1, x^n*(x-1)^(n+1)/n.factorial * (exp x)


--facts about these integrals
lemma A0 : A 0 = e - 1 := by
  rw [A]
  simp
  rfl

lemma B0 : B 0 = 1 := by
  rw[B]
  simp
  rw [integration_by_parts_left 0 1]
  ring_nf
  simp

lemma C0 : C 0 = 2 - e := by
  rw[C]
  simp
  have H : ∫ (x : ℝ) in (0: ℝ)..1, (x - 1) * Real.exp x = (∫ (x : ℝ) in (0: ℝ)..1, x * Real.exp x)
            - ∫ (x : ℝ) in (0: ℝ)..1, Real.exp x
  . rw [←integral_sub]
    congr
    funext
    ring
    . apply Continuous.intervalIntegrable
      . apply Continuous.mul
        . exact continuous_id
        . exact continuous_exp
    . apply Continuous.intervalIntegrable
      . apply continuous_exp
  rw[H]
  rw [integration_by_parts_left 0 1]
  simp
  rw[e]
  ring

lemma A_rec_help(n : ℕ) : A (n+1) + B n + C n = 0 := by
  rw[A, B, C]
  rw[← integral_add]
  rw[← integral_add]
  let f: ℝ → ℝ := λ x => x^(n+1)*(x-1)^(n+1)* e^x/(n+1).factorial
  convert integral_deriv_eq_sub' f _ _ _
  simp
  sorry
  --apply DifferentiableAt.mul
  sorry
  sorry
  repeat' apply Continuous.intervalIntegrable
  repeat' continuity

lemma A_rec (n : ℕ) : A (n+1) = - B n - C n := by
  linarith [A_rec_help n]

lemma B_rec_help (n: ℕ): B (n + 1) + 2*(n+1)*(A (n + 1)) - C n = 0:= by
  rw[A, B, C]
  sorry


lemma B_rec (n : ℕ) : B (n+1) = -2*(n+1)*(A (n + 1)) + (C n) := by
  linarith [B_rec_help n]

lemma C_rec (n : ℕ) : C n = B n - A n := by
  rw[C, A, B]
  rw[←integral_sub _ _]
  congr
  funext
  ring
  repeat' apply Continuous.intervalIntegrable
  repeat' continuity

lemma big_rec (n : ℕ) : A n = (Q (3*n))*e - P (3*n) ∧ B n = (P (3*n+1))*e - (Q (3*n+1))*e
                    ∧ C n = P (3*n+2) - (Q (3*n+2))*e := sorry
/-
Step 3: putting it all together
-/
open Filter Topology

--limits of the integrals
lemma A_lim : Tendsto A atTop (𝓝 0) := sorry
lemma B_lim : Tendsto B atTop (𝓝 0) := sorry
lemma C_lim : Tendsto C atTop (𝓝 0) := sorry

--the main theorem
theorem e_CF : Tendsto (λ i => (conv e_seq i : ℝ)) atTop (𝓝 e) := sorry


--a bunch of tests working with Filters

--(x⁻¹) → 0 as x → ∞
example : Tendsto (λ x : ℝ => x⁻¹) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero

--1/x → 0 as x → ∞
example : Tendsto (λ x : ℝ => 1/x) atTop (𝓝 0) := by
  simp; exact tendsto_inv_atTop_zero

--same thing, but now x is in ℕ
example : Tendsto (λ x : ℕ => (x : ℝ)⁻¹) atTop (𝓝 0) := by
  apply Tendsto.comp tendsto_inv_atTop_zero
  apply tendsto_nat_cast_atTop_atTop

example (f : ℝ → ℝ) (g : ℝ → ℝ) (H : ∀ᶠ x in atTop, f x = g x) (hf : Tendsto f atTop atTop)
        : Tendsto g atTop atTop := by
      exact Tendsto.congr' H hf

--showing that some function which is eventually equal to 1/x goes to 0
example : Tendsto (λ x : ℕ => if x < 10 then (x : ℝ) else (x : ℝ)⁻¹) atTop (𝓝 0) := by
  have H : (λ x : ℕ => (x : ℝ)⁻¹) =ᶠ[atTop] (λ x => if x < 10 then (x : ℝ) else (x : ℝ)⁻¹)
  . rw [eventuallyEq_iff_exists_mem]
    use {x : ℕ | x ≥ 10}
    apply And.intro
    . simp; use 10; simp
    . intro x (hx : x ≥ 10)
      simp [hx]
      have H₁ : ¬(x < 10)
      . linarith
      simp [H₁]
  apply Tendsto.congr'
  apply H
  apply Tendsto.comp tendsto_inv_atTop_zero
  apply tendsto_nat_cast_atTop_atTop

--100/x → 0 as x → ∞
example : Tendsto (λ x : ℝ => 100/x) atTop (𝓝 0) := by
  have H₁ : Tendsto (λ _ : ℝ => (100 : ℝ)) atTop (𝓝 100) := tendsto_const_nhds
  have H₂ : Tendsto (λ x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  convert Tendsto.mul H₁ H₂ using 2
  simp

--squeeze theorem
example (f : ℝ → ℝ) (hf₁ : f ≥ 0) (hf₂ : ∀ x ≥ 0, f x ≤ x⁻¹) : Tendsto f atTop (𝓝 0) := by
  have hg : Tendsto (λ x : ℝ => (0 : ℝ)) atTop (𝓝 0) := by simp
  have hh : Tendsto (λ x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh
  simp; use 0; intro b _; apply hf₁
  simp; use 0
