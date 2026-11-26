import Singular
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section
open Matrix
namespace ERK.Transport

variable {i j k : Type*} [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j]
    [Fintype k] [DecidableEq k]

/-- The complex matrix of a real continuous linear map in the coordinate bases. -/
def mat (L : (i → ℝ) →L[ℝ] (j → ℝ)) : Matrix j i ℂ :=
  (LinearMap.toMatrix' L.toLinearMap).map Complex.ofRealHom

omit [Fintype k] [DecidableEq k] in
theorem mat_comp (L : (j → ℝ) →L[ℝ] (k → ℝ)) (R : (i → ℝ) →L[ℝ] (j → ℝ)) :
    mat (L.comp R) = mat L * mat R := by
  unfold mat
  rw [show (L.comp R).toLinearMap = L.toLinearMap.comp R.toLinearMap from rfl,
    LinearMap.toMatrix'_comp, Matrix.map_mul]

theorem mat_id : mat (ContinuousLinearMap.id ℝ (i → ℝ)) = (1 : Matrix i i ℂ) := by
  unfold mat
  rw [show (ContinuousLinearMap.id ℝ (i → ℝ)).toLinearMap = LinearMap.id from rfl,
    LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero _) (map_one _)]

omit [Fintype j] [DecidableEq j] in
theorem mat_smul (s : ℝ) (L : (i → ℝ) →L[ℝ] (j → ℝ)) :
    mat (s • L) = (s:ℂ) • mat L := by
  ext a b
  simp [mat, Matrix.smul_apply]

/-- Change of coordinates may also change the finite index type. -/
theorem hurwitz_conjugate (P : Matrix j i ℂ) (Q : Matrix i j ℂ)
    (hPQ : P*Q=1) (hQP : Q*P=1) (A : Matrix i i ℂ) (hA : Singular.Hurwitz A) :
    Singular.Hurwitz (P*A*Q) := by
  intro z hz
  let M := A-z • 1
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr (hA z hz)
  have heq : P*A*Q-z • 1 = P*M*Q := by
    simp [M, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hPQ]
  rw [heq]
  apply Matrix.det_ne_zero_of_right_inverse (B := P*M⁻¹*Q)
  calc
    P*M*Q*(P*M⁻¹*Q) = P*(M*(Q*P)*M⁻¹)*Q := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hQP, Matrix.mul_one, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one, hPQ]

/-- A positive time change and an invertible linear chart preserve class stability.
The matrix on either side is built from the Fréchet derivative of that actual field. -/
theorem change_of_coordinates (E : (i → ℝ) ≃L[ℝ] (j → ℝ))
    (f : (i → ℝ) → i → ℝ) (g : (j → ℝ) → j → ℝ) (x : i → ℝ)
    (s : ℝ) (hs : 0 < s) (hf : DifferentiableAt ℝ f x)
    (hc : ∀ v, g (E v) = s • E (f v))
    (hH : Singular.Hurwitz (mat (fderiv ℝ f x))) :
    Singular.Hurwitz (mat (fderiv ℝ g (E x))) := by
  let P := (E : (i → ℝ) →L[ℝ] (j → ℝ))
  let Q := (E.symm : (j → ℝ) →L[ℝ] (i → ℝ))
  have pq : P.comp Q = ContinuousLinearMap.id ℝ (j → ℝ) := by ext1 v; exact E.apply_symm_apply v
  have qp : Q.comp P = ContinuousLinearMap.id ℝ (i → ℝ) := by ext1 v; exact E.symm_apply_apply v
  have hP : mat P * mat Q = 1 := by rw [← mat_comp,pq,mat_id]
  have hQ : mat Q * mat P = 1 := by rw [← mat_comp,qp,mat_id]
  have he : g = fun v => s • E (f (E.symm v)) := by
    funext v
    simpa using hc (E.symm v)
  have hf' : HasFDerivAt f (fderiv ℝ f x) (E.symm (E x)) := by simpa using hf.hasFDerivAt
  have hder : fderiv ℝ g (E x) = s • (P.comp ((fderiv ℝ f x).comp Q)) := by
    rw [he]
    exact ((P.hasFDerivAt.comp _ (hf'.comp _ Q.hasFDerivAt)).const_smul s).fderiv
  rw [hder,mat_smul,mat_comp,mat_comp,← Matrix.mul_assoc]
  exact Singular.hurwitz_pos_smul _ (hurwitz_conjugate _ _ hP hQ _ hH) _ hs

#print axioms hurwitz_conjugate
#print axioms change_of_coordinates

end ERK.Transport
