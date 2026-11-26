import Model
import Lift
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Filter Matrix
open scoped Topology
namespace ERK.Second
open Model

/-- The block-diagonal Jacobian in the physical ordering of the six bound enzyme
complexes after eliminating the two free enzyme totals. -/
def fastMatrix (K δ A B C D : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  let a := K*A
  let b := C/δ
  let c := D/δ
  let f := K*B
  let l := 1/δ
  !![-a-1,-a,-a,0,0,0; 1-b,-b-l,-b,0,0,0; -c,-c,-c-l,0,0,0;
    0,0,0,-f-1,-f,-f; 0,0,0,1,-l,0; 0,0,0,-b,-b,-b-l]

def atFastMatrix (K δ : ℝ) (x : I → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  let y := toSlow δ (x ∘ Sum.inl)
  fastMatrix K δ (freeA y) (y 0) (y 1) (y 2)

def insertFast (v : Bound) : I → ℝ := Sum.elim 0 v

set_option maxHeartbeats 800000 in
/-- Exact directional increments at zero total-enzyme parameter. Terms due
to the sequestered substrate vanish at precisely eta = 0. -/
theorem fast_increment (p q K δ s : ℝ) (x : I → ℝ) (v : Bound) (t : ℝ) :
    (etaEq p q K δ s (0,x+t • insertFast v)) ∘ Sum.inr =
      etaEq p q K δ s (0,x) ∘ Sum.inr + t • (atFastMatrix K δ x).mulVec v := by
  funext i
  fin_cases i <;>
    simp [etaEq,enzymeRHS,insertFast,classA,freeA,freeE,freeF,toSlow,
      atFastMatrix,fastMatrix,dotProduct,Fin.sum_univ_succ,div_eq_mul_inv] <;> ring

theorem fast_fderiv (p q K δ s : ℝ) (x : I → ℝ) (v : Bound)
    (hH : DifferentiableAt ℝ (etaEq p q K δ s) (0,x)) :
    (fderiv ℝ (etaEq p q K δ s) (0,x) (0, insertFast v)) ∘ Sum.inr =
      (atFastMatrix K δ x).mulVec v := by
  let H := etaEq p q K δ s
  let path := fun t : ℝ => ((0:ℝ), x+t • insertFast v)
  have hp : HasDerivAt path (0,insertFast v) 0 := by
    apply (hasDerivAt_const (0:ℝ) (0:ℝ)).prodMk
    simpa using (((hasDerivAt_id' (0:ℝ)).smul_const (insertFast v)).const_add x)
  have h0 : path 0 = (0,x) := by simp [path]
  have hcomp := hH.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hp h0.symm
  funext i
  have hl := hasDerivAt_pi.mp hcomp (.inr i)
  have hr : HasDerivAt (fun t : ℝ => H (0,x) (.inr i) + t*((atFastMatrix K δ x).mulVec v i))
      ((atFastMatrix K δ x).mulVec v i) 0 := by
    simpa using (((hasDerivAt_id' (0:ℝ)).mul_const ((atFastMatrix K δ x).mulVec v i)).const_add
      (H (0,x) (.inr i)))
  exact hl.unique (hr.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t => congrFun (fast_increment p q K δ s x v t) i)))


end ERK.Second
