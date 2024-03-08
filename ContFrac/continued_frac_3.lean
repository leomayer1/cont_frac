import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Tactic
import Mathlib.Analysis.Convolution
import Mathlib.Data.Matrix.Basic



def ContFrac := ℕ → ℕ

--i-th convergent, as a list
def list_of_CF (a : ContFrac) : ℕ → List ℚ
  | 0 => [a 0]
  | (n+1) => (list_of_CF a n) ++ [(a (n+1) : ℚ)]

#eval list_of_CF (λ n => n^2) 10

--from a finite continued fraction to a rational
def conv_of_list : List ℚ  → ℚ
| [] => 0
| [n] => n
| (n :: l) => n + 1/(conv_of_list l)

noncomputable def conv_of_list_inf : List ℚ → ℝ
| [] => 0
| [n] => n
| (n :: l) => n + 1/(conv_of_list l)


variable (a : ContFrac) (i : ℕ)
def conv : ℚ := conv_of_list (list_of_CF a i)

def e_seq : ContFrac := λ x => if x % 3 = 1 then 2*(x-1)/3 else 1



def p (a : ContFrac) : ℕ → ℕ
| 0 => a 0
| 1 => (a 0)*(a 1) + 1
| (n + 2) => (a (n + 2))*(p a (n + 1)) + p a n

def q (a : ContFrac) : ℕ → ℕ
| 0 => 1
| 1 => a 1
| (n + 2) => (a (n + 2))*(q a (n + 1)) + q a n

def mat_base (a : ContFrac): (Fin 2) → (Fin 2) → ℕ
| 0 => λ x => if x = 0 then 1 else a 0
| 1 => λ x => if x = 0 then 0 else 1

def mat_2 (a : ContFrac) (i: ℕ): (Fin 2) → (Fin 2) → ℕ
| 0 => λ x => if x = 0 then 0 else 1
| 1 => λ x => if x = 0 then 1 else a i

def M: Matrix (Fin 2) (Fin 2) ℕ := Matrix.of mat_2 e_seq  1
def m_base: Matrix (Fin 2) (Fin 2) ℕ := Matrix.of mat_base e_seq
#eval m_base * M


def rs (i : ℕ )(a: ContFrac ): ℕ  → ℕ × ℕ
| 0 => (1, a i)
| (n + 1) => ((rs i a n).snd, (rs i a n).fst * a (i - n) + (rs i a n).snd)

@[simp]
lemma rs_n_plus_1 (n : ℚ)(i : ℕ )(a: ContFrac ) : rs (n + 1) = ((rs i a n).snd, (rs i a n).fst * a (i - n) + (rs i a n).snd) := by
  sorry

#eval (rs 9 e_seq 9).fst
--vector based on r and s

#eval p e_seq 0
#eval e_seq 0 ≠ 0

--Define P that is multiplication of n matrices
--def P (a : ContFrac): ℕ → ((Fin 2) → (Fin 2) → ℕ)
  --| 0 => mat_base a
  --| (n + 1) => (P a n) * (mat_2 a (n+1))
def P (a : ContFrac): ℕ → Matrix (Fin 2) (Fin 2) ℕ
| 0 => Matrix.of mat_base a
| (n + 1) => (P a n) * Matrix.of (mat_2 a (n+1))

def pq (a : ContFrac)(i: ℕ): (Fin 2) → (Fin 2) → ℕ
| 0 => λ x => if x = 0 then p a i  else p a (i+1)
| 1 => λ x => if x = 0 then q a i else q a (i+1)



#eval P e_seq 1
#eval p e_seq 2
#eval q e_seq 2
#eval e_seq 10

--lemma: in P the second column is pn qn, which shows the construction of P makes sense
lemma P_pn (a: ContFrac) (i: ℕ): P a (i + 1) = Matrix.of pq a i:= by
  simp
  induction i
  unfold P
  unfold pq
  simp
  sorry
  sorry


theorem finite_converged (a: ContFrac) (i: ℕ) (h: ∀ n ≤ i, a n > 0): conv a i = p a i / q a i := by
  induction i
  unfold conv
  unfold list_of_CF
  unfold conv_of_list
  unfold p
  unfold q
  simp
  sorry

-- continued fraction for √2
def sqrt_2: ContFrac := λ x => if x == 0 then 1 else 2
#eval list_of_CF (sqrt_2) 10
-- continued fraction for √3
def sqrt_3: ContFrac := λ x => if x == 0 then 1 else if x % 2 = 1 then 1 else 2
#eval list_of_CF (sqrt_3) 10

--lemma contfrac_sqrt2 (sqrt_2: ContFrac): conv_of_list (list_of_CF sqrt_2) = √2 :=by

-- simp the rs function for proving the consequent lemma
-- @[simp]
-- lemma rs_n_plus_1 (i : ℕ )(a: ContFrac ) : rs (n + 1) = ((rs i a n).snd, (rs i a n).fst * a (i - n) + (rs i a n).snd) := by
--   sorry


lemma rs_i1 (i : ℕ )(a: ContFrac ) : rs (i + 1) = Matrix.of rs i := by
  induction i
  simp
  simp
  rw
  sorry
