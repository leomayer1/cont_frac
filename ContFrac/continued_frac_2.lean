import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Tactic
import Mathlib.Analysis.Convolution
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation


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


lemma element_fin2 (x: Fin 2): (x = 1 ) ∨ (x = 0 ):= by
rcases x with ⟨x, hx ⟩
cases' x with y
. right; rfl
cases' y with z
. left; rfl
exfalso
have H: z.succ.succ ≥ 2
show 2 ≤ z+2; simp
apply Nat.not_lt_of_ge H hx

#check Matrix (Fin 2)  (Fin 2 ) (ℕ)

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

def vecrs (i : ℕ )(n: ℕ )(a: ContFrac ): (Fin 2) → (Fin 1) → ℕ
| 0 => (rs i a n).fst
| 1 => (rs i a n).snd

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

lemma matrix_mul(A: Matrix (Fin 2) (Fin 2) ℕ)(B: Matrix (Fin 2) (Fin 2) ℕ):
A * B = !![A 0 0 * B 0 0 + A 0 1 * B 1 0, A 0 0 * B 0 1 + A 0 1 * B 1 1;
A 1 0 * B 0 0 + A 1 1 * B 1 0, A 1 0 * B 0 1 + A 1 1 * B 1 1]:=by
exact Matrix.eta_fin_two (A * B)

lemma foo (a : ContFrac): mat_base a 1 0 = 0 := by
  unfold mat_base
  econstructor


--lemma: in P the second column is pn qn, which shows the construction of P makes sense
lemma P_pn (a: ContFrac) (i: ℕ): P a (i + 1) = Matrix.of pq a i:= by
  induction i
  unfold P
  unfold pq
  simp
  funext n m
  have h: n = 1 ∨ n = 0 := element_fin2 n
  --have isltn: n < 2
  have h': m = 1 ∨ m = 0 := element_fin2 m
  rcases h with n1 | n2
  rcases h' with m1 | m2
  . rw[n1, m1, matrix_mul]
    simp[P]
    have: mat_base a 1 0 = 0:= by
      unfold mat_base
      econstructor
    rw[this]
    simp
    have: mat_base a 1 1 = 1:= by
      unfold mat_base
      econstructor
    rw[this]
    have: mat_2 a 1 1 1 = a 1:= by
      unfold mat_2
      econstructor
    rw[this]
    simp
    econstructor
  . rw[n1, m2, matrix_mul]
    simp[P]



  --simp[P, pq]
  --have: (P a 0 * Matrix.of (mat_2 a 1)) 1 1  = a 1:= by

  --unfold Matrix.of mat_base *

  --rcases m
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
