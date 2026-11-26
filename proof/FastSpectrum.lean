import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
open Matrix
namespace ERK.Fast

/-- A quadratic with strictly positive real coefficients is Hurwitz. -/
theorem quadratic (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ)
    (hz : z*z + (a:ℂ)*z + b = 0) : z.re < 0 := by
  by_contra! h
  have hi := congrArg Complex.im hz
  have hr := congrArg Complex.re hz
  simp [Complex.mul_im] at hi
  simp [Complex.mul_re] at hr
  have hp : 0 < 2*z.re + a := by linarith
  have hprod : (2*z.re+a)*z.im = 0 := by linarith
  have him := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hp)
  rw [him] at hr
  nlinarith [mul_nonneg ha.le h, sq_nonneg z.re]

/-- Frozen complex concentrations u,v,w, after eliminating free enzyme by its total.
a is the first association strength, b,c the two remaining association strengths.
The first bound state transfers to the second at unit rate; g is the total exit
rate of each of the last two states. -/
def enzyme (a b c g : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-(a:ℂ)-1, -a, -a; 1-b, -b-g, -b; -c, -c, -c-g]

theorem enzyme_det (a b c g : ℝ) (z : ℂ) :
    (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - enzyme a b c g).det =
    (z+g)*(z*z+((a+1+b+c+g : ℝ):ℂ)*z+(((a+1)*g+b+c+a : ℝ):ℂ)) := by
  simp [Matrix.det_fin_three, enzyme, Matrix.sub_apply, Matrix.smul_apply]
  ring

theorem enzyme_hurwitz (a b c g : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hg : 0 < g) (z : ℂ)
    (hz : (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) - enzyme a b c g).det = 0) : z.re < 0 := by
  rw [enzyme_det] at hz
  rcases mul_eq_zero.mp hz with h | h
  · have hr := congrArg Complex.re h
    simp at hr
    linarith
  · exact quadratic _ _ (by positivity) (by positivity) z h

/-- Both free singly-modified substrates on the rescaled critical graph. -/
def substrates (p e f : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-((p*e+f:ℝ):ℂ), 0; 0, -(e:ℂ)]

theorem substrates_hurwitz (p e f : ℝ) (hp : 0 < p) (he : 0 < e) (hf : 0 < f)
    (z : ℂ) (hz : (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - substrates p e f).det = 0) :
    z.re < 0 := by
  have fac : (z + ((p*e+f:ℝ):ℂ))*(z+(e:ℂ)) = 0 := by
    have heq : (z • (1 : Matrix (Fin 2) (Fin 2) ℂ) - substrates p e f).det =
        (z + ((p*e+f:ℝ):ℂ))*(z+(e:ℂ)) := by
      rw [Matrix.det_fin_two]
      change (z * 1 - -((p*e+f : ℝ) : ℂ)) * (z * 1 - -(e:ℂ)) -
        (z*0-0)*(z*0-0) = _
      ring
    exact heq.symm.trans hz
  rcases mul_eq_zero.mp fac with h|h
  · have hr := congrArg Complex.re h
    simp at hr
    nlinarith [mul_pos hp he]
  · have hr := congrArg Complex.re h
    simp at hr
    linarith

/-- The six enzyme directions at every positive substrate state, for fixed positive δ and K. -/
theorem both_enzyme_blocks (A B C D K δ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D)
    (hK : 0 < K) (hδ : 0 < δ) :
    (∀ z : ℂ, (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      enzyme (K*A) (C/δ) (D/δ) (1/δ)).det = 0 → z.re < 0) ∧
    (∀ z : ℂ, (z • (1 : Matrix (Fin 3) (Fin 3) ℂ) -
      enzyme (K*B) 0 (C/δ) (1/δ)).det = 0 → z.re < 0) := by
  constructor <;> apply enzyme_hurwitz <;> positivity

#print axioms quadratic
#print axioms enzyme_det
#print axioms enzyme_hurwitz
#print axioms substrates_hurwitz
#print axioms both_enzyme_blocks
end ERK.Fast
