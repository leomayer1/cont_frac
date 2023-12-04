/-
Following the exposition from https://arxiv.org/pdf/math/0601660.pdf
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Instances.Real
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


lemma conv_rec : p a (i+2) = (a (i+2))*(p a (i+1)) + p a (i)
  ∧ q a (i+2) = (a (i+2))*(q a (i+1)) + q a (i) := ⟨rfl, rfl⟩

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
def e_seq : ℕ → ℕ := sorry
def P := p e_seq
def Q := q e_seq
noncomputable def e := Real.exp 1


--have a bunch of recurrence relations for the p_i and q_i
lemma P0 (n : ℕ) : P (3*n+3) = P (3*n + 2) + P (3*n + 1) := sorry
lemma P1 (n : ℕ) : P (3*n+4) = 2*n*(P (3*n + 3)) + P (3*n + 2) := sorry
lemma P2 (n : ℕ) : P (3*n+2) = P (3*n + 1) + P (3*n) := sorry

lemma Q0 (n : ℕ) : Q (3*n+3) = Q (3*n + 2) + Q (3*n + 1) := sorry
lemma Q1 (n : ℕ) : Q (3*n+4) = 2*n*(Q (3*n + 3)) + Q (3*n + 2) := sorry
lemma Q2 (n : ℕ) : Q (3*n+2) = Q (3*n + 1) + Q (3*n) := sorry

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

example (a b : ℝ) : (∫ x in a..b, x*(exp x)) = (b*(exp b) - exp b) - (a*(exp a) - exp a) := by
  rw [integral_mul_deriv_eq_deriv_mul (v := exp) (u' := 1)]
  simp [one_mul]
  ring
  sorry
  sorry
  sorry
  sorry

--magical integrals
noncomputable def A (n : ℕ) := ∫ x in (0 : ℝ)..1, (exp x)*x^n*(x-1)^n/n.factorial
noncomputable def B (n : ℕ) := ∫ x in (0 : ℝ)..1, (exp x)*x^(n+1)*(x-1)^n/n.factorial
noncomputable def C (n : ℕ) := ∫ x in (0 : ℝ)..1, (exp x)*x^n*(x-1)^(n+1)/n.factorial

--facts about these integrals
lemma A0 : A 0 = e - 1 := sorry
lemma B0 : B 0 = 1 := sorry
lemma C0 : C 0 = 2 - e := sorry

lemma A_rec (n : ℕ) : A (n+1) = - B n - C n := sorry
lemma B_rec (n : ℕ) : B (n+1) = -2*(n+1)*(A (n + 1)) + (C n) := sorry
lemma C_rec (n : ℕ) : C n = B n - A n := sorry

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
