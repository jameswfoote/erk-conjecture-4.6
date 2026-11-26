import Singular
import Continuation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

/-! A local equilibrium branch for fast-slow finite-dimensional ODEs,
with spectral stability of its actual dynamical Jacobian. -/
noncomputable section
open Filter Matrix Set
open scoped Topology
namespace ERK.Lift

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

abbrev Space (m n : Type*) := (m ⊕ n) → ℝ

/-- Complexified coordinate matrix of a real linear map in the canonical basis. -/
def matrixOf {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (L : (a → ℝ) →L[ℝ] (b → ℝ)) : Matrix b a ℂ :=
  (LinearMap.toMatrix' L.toLinearMap).map Complex.ofReal

@[simp] theorem matrixOf_apply {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (L : (a → ℝ) →L[ℝ] (b → ℝ)) (i : b) (j : a) :
    matrixOf L i j = (L (Pi.single j 1) i : ℝ) := by
  change (LinearMap.toMatrix' L.toLinearMap i j : ℂ) = _
  rw [LinearMap.toMatrix'_apply]
  have he : (fun k => if k = j then (1 : ℝ) else 0) = Pi.single j 1 := by
    funext k
    simp [Pi.single_apply]
  rw [he]
  rfl

/-- The complexified partial Jacobian, keeping the time parameter fixed. -/
def stateMatrix (H : ℝ × Space m n → Space m n) (v : ℝ × Space m n) :=
  matrixOf ((fderiv ℝ H v).comp (ContinuousLinearMap.inr ℝ ℝ (Space m n)))

/-- Restore the fast time scale to the lower block row. -/
def rowMap (t : ℝ) : Space m n →L[ℝ] Space m n :=
  ContinuousLinearMap.pi (Sum.elim (fun i => ContinuousLinearMap.proj (R := ℝ) (Sum.inl i))
    (fun j => t⁻¹ • ContinuousLinearMap.proj (R := ℝ) (Sum.inr j)))

def field (H : ℝ × Space m n → Space m n) (t : ℝ) (x : Space m n) :=
  rowMap t (H (t,x))

def blockData (t : ℝ) (J : Matrix (m ⊕ n) (m ⊕ n) ℂ) : Singular.Data m n :=
  (t,J.toBlocks₁₁,J.toBlocks₁₂,J.toBlocks₂₁,J.toBlocks₂₂)

theorem matrix_field (H : ℝ × Space m n → Space m n) (t : ℝ) (x : Space m n)
    (hd : DifferentiableAt ℝ H (t,x)) :
    matrixOf (fderiv ℝ (field H t) x) = Singular.jacobian (blockData t (stateMatrix H (t,x))) := by
  have hb : HasFDerivAt (fun y : Space m n => (t,y))
      (ContinuousLinearMap.inr ℝ ℝ (Space m n)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hf := (rowMap (m := m) (n := n) t).hasFDerivAt.comp x (hd.hasFDerivAt.comp x hb)
  change matrixOf (fderiv ℝ (fun y => rowMap t (H (t,y))) x) = _
  rw [show fderiv ℝ (fun y => rowMap t (H (t,y))) x =
      (rowMap t).comp ((fderiv ℝ H (t,x)).comp (ContinuousLinearMap.inr ℝ ℝ (Space m n))) from hf.fderiv]
  ext (i|i) (j|j) <;> simp [Singular.jacobian, blockData, stateMatrix, rowMap,
    Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem continuousAt_stateMatrix (H : ℝ × Space m n → Space m n) (v : ℝ × Space m n)
    (h : ContDiffAt ℝ 1 H v) : ContinuousAt (stateMatrix H) v := by
  have hd : ContinuousAt (fderiv ℝ H) v := (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  simp only [stateMatrix, matrixOf_apply, ContinuousLinearMap.comp_apply]
  exact Complex.continuous_ofReal.continuousAt.comp <|
    (continuous_apply i).continuousAt.comp (hd.clm_apply continuousAt_const)

private theorem det_ne_zero (J : Matrix (m ⊕ n) (m ⊕ n) ℂ)
    (hD : Singular.Hurwitz J.toBlocks₂₂)
    (hS : Singular.Hurwitz (J.toBlocks₁₁ - J.toBlocks₁₂ * J.toBlocks₂₂⁻¹ * J.toBlocks₂₁)) :
    J.det ≠ 0 := by
  have hd : J.toBlocks₂₂.det ≠ 0 := by simpa using hD 0 (by simp)
  have hs : (J.toBlocks₁₁ - J.toBlocks₁₂ * J.toBlocks₂₂⁻¹ * J.toBlocks₂₁).det ≠ 0 := by
    simpa using hS 0 (by simp)
  letI := (J.toBlocks₂₂.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd)).invertible
  calc J.det = (fromBlocks J.toBlocks₁₁ J.toBlocks₁₂ J.toBlocks₂₁ J.toBlocks₂₂).det := by
         rw [fromBlocks_toBlocks]
       _ = _ := Matrix.det_fromBlocks₂₂ _ _ _ _
       _ ≠ 0 := mul_ne_zero hd (by simpa only [Matrix.invOf_eq_nonsing_inv] using hs)

/-- A positive-time equilibrium branch whose actual rescaled Jacobian stays Hurwitz.
Only local C¹ regularity of the unscaled equations at the limiting zero is required. -/
theorem stable_branch (H : ℝ × Space m n → Space m n) (x : Space m n)
    (hz : H (0,x) = 0) (hC : ContDiffAt ℝ 1 H (0,x))
    (hD : Singular.Hurwitz (stateMatrix H (0,x)).toBlocks₂₂)
    (hS : let J := stateMatrix H (0,x)
          Singular.Hurwitz (J.toBlocks₁₁ - J.toBlocks₁₂ * J.toBlocks₂₂⁻¹ * J.toBlocks₂₁)) :
    ∃ u : ℝ → Space m n, u 0 = x ∧ ContinuousAt u 0 ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), H (t,u t) = 0 ∧ field H t (u t) = 0 ∧
        Singular.Hurwitz (matrixOf (fderiv ℝ (field H t) (u t))) := by
  let P := fderiv ℝ H (0,x)
  let L := P.comp (ContinuousLinearMap.inr ℝ ℝ (Space m n))
  let N := P.comp (ContinuousLinearMap.inl ℝ ℝ (Space m n))
  have hdet := det_ne_zero (stateMatrix H (0,x)) hD hS
  have hl : L.det ≠ 0 := by
    change (Complex.ofRealHom.mapMatrix (LinearMap.toMatrix' L.toLinearMap)).det ≠ 0 at hdet
    rw [← Complex.ofRealHom.map_det, LinearMap.det_toMatrix'] at hdet
    exact fun h => hdet (by simpa [L,P] using congrArg Complex.ofReal h)
  let E := L.toContinuousLinearEquivOfDetNeZero hl
  have hsplit : (E : Space m n →L[ℝ] Space m n).comp (ContinuousLinearMap.snd ℝ ℝ (Space m n)) +
      N.comp (ContinuousLinearMap.fst ℝ ℝ (Space m n)) = P := by
    simp only [E, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    apply ContinuousLinearMap.ext
    intro v
    change P (0,v.2) + P (v.1,0) = _
    rw [← map_add]
    congr 1
    ext <;> simp
  have hprime := hC.hasStrictFDerivAt (by norm_num)
  obtain ⟨u,hu,huc,huz⟩ := Lifting.equilibrium_branch H x hz N E (hsplit.symm ▸ hprime)
  refine ⟨u,hu,huc,?_⟩
  have harg : Tendsto (fun t => (t,u t)) (𝓝[>] (0 : ℝ)) (𝓝 (0,x)) :=
    (tendsto_id.prodMk_nhds (hu ▸ huc.tendsto)).mono_left nhdsWithin_le_nhds
  have hJ := (continuousAt_stateMatrix H (0,x) hC).tendsto.comp harg
  have hdata : Continuous (fun v : ℝ × Matrix (m ⊕ n) (m ⊕ n) ℂ => blockData v.1 v.2) := by
    unfold blockData
    refine continuous_fst.prodMk (Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)))
    all_goals
      apply continuous_matrix
      intro i j
      exact (continuous_snd.matrix_elem _ _)
  have hnear := hdata.continuousAt.tendsto.comp ((tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hJ)
  have hs := hnear.eventually (Singular.eventually_hurwitz _ _ _ _ hD hS)
  have hdiff := harg.eventually ((hC.eventually (by simp)).mono (fun _ h => h.differentiableAt_one))
  filter_upwards [hs, huz.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin, hdiff] with t ht hzero htpos hdiff'
  refine ⟨hzero, by simp [field,hzero], ?_⟩
  rw [matrix_field H t (u t) hdiff']
  exact ht htpos

#print axioms stable_branch

theorem matrixOf_comp {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (P : (b → ℝ) →L[ℝ] (c → ℝ)) (Q : (a → ℝ) →L[ℝ] (b → ℝ)) :
    matrixOf (P.comp Q) = matrixOf P * matrixOf Q := by
  change (LinearMap.toMatrix' (P.toLinearMap.comp Q.toLinearMap)).map Complex.ofRealHom = _
  rw [LinearMap.toMatrix'_comp, Matrix.map_mul]
  rfl

private def paste {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X →L[ℝ] (m → ℝ)) (g : X →L[ℝ] (n → ℝ)) : X →L[ℝ] Space m n :=
  ContinuousLinearMap.pi (Sum.elim (fun i => (ContinuousLinearMap.proj i).comp f)
    (fun i => (ContinuousLinearMap.proj i).comp g))

omit [DecidableEq m] [DecidableEq n] in
private theorem paste_hasFDerivAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → m → ℝ} {g : X → n → ℝ} {P : X →L[ℝ] (m → ℝ)} {Q : X →L[ℝ] (n → ℝ)}
    {x : X} (hf : HasFDerivAt f P x) (hg : HasFDerivAt g Q x) :
    HasFDerivAt (fun y => Sum.elim (f y) (g y)) (paste P Q) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  cases i with
  | inl i => exact (hasFDerivAt_apply i (f x)).comp x hf
  | inr i => exact (hasFDerivAt_apply i (g x)).comp x hg

/-- Differentiating the critical-graph identity identifies the Schur complement
with the actual derivative of the reduced field in slow coordinates. -/
theorem schur_on_graph (H : ℝ × Space m n → Space m n) (g : (m → ℝ) → (n → ℝ))
    (R : (m → ℝ) → (m → ℝ)) (x : m → ℝ)
    (hdH : DifferentiableAt ℝ H (0,Sum.elim x (g x)))
    (hdg : DifferentiableAt ℝ g x) (hdR : DifferentiableAt ℝ R x)
    (hgraph : ∀ᶠ y in 𝓝 x, H (0,Sum.elim y (g y)) = Sum.elim (R y) 0)
    (hfast : Singular.Hurwitz (stateMatrix H (0,Sum.elim x (g x))).toBlocks₂₂) :
    let J := stateMatrix H (0,Sum.elim x (g x))
    J.toBlocks₁₁ - J.toBlocks₁₂ * J.toBlocks₂₂⁻¹ * J.toBlocks₂₁ = matrixOf (fderiv ℝ R x) := by
  let G := fderiv ℝ g x
  let T := fderiv ℝ R x
  let Y := Sum.elim x (g x)
  let P := (fderiv ℝ H (0,Y)).comp (ContinuousLinearMap.inr ℝ ℝ (Space m n))
  let J := matrixOf P
  let U := paste (ContinuousLinearMap.id ℝ (m → ℝ)) G
  let V := paste T (0 : (m → ℝ) →L[ℝ] (n → ℝ))
  have hU : HasFDerivAt (fun y => Sum.elim y (g y)) U x :=
    paste_hasFDerivAt (hasFDerivAt_id x) hdg.hasFDerivAt
  have hV : HasFDerivAt (fun y => Sum.elim (R y) (0 : n → ℝ)) V x :=
    paste_hasFDerivAt hdR.hasFDerivAt (hasFDerivAt_const (0 : n → ℝ) x)
  have hemb : HasFDerivAt (fun y : Space m n => ((0:ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ (Space m n)) Y :=
    (hasFDerivAt_const (0:ℝ) Y).prodMk (hasFDerivAt_id Y)
  have hP : HasFDerivAt (fun y : Space m n => H (0,y)) P Y := hdH.hasFDerivAt.comp Y hemb
  have hL : HasFDerivAt (fun y => H (0,Sum.elim y (g y))) (P.comp U) x :=
    HasFDerivAt.comp (g := fun y : Space m n => H (0,y)) (f := fun y : m → ℝ => Sum.elim y (g y))
      (g' := P) (f' := U) x hP hU
  change (fun y => H (0,Sum.elim y (g y))) =ᶠ[𝓝 x] (fun y => Sum.elim (R y) 0) at hgraph
  have he : P.comp U = V := hL.fderiv.symm.trans (hgraph.fderiv_eq.trans hV.fderiv)
  have hm : J * matrixOf U = matrixOf V := (matrixOf_comp P U).symm.trans (congrArg matrixOf he)
  have eu (i j : m) : matrixOf U (Sum.inl i) j = if i = j then 1 else 0 := by
    by_cases h : i = j <;> simp [U,paste,h]
  have ew (i : n) (j : m) : matrixOf U (Sum.inr i) j = matrixOf G i j := rfl
  have ev (i j : m) : matrixOf V (Sum.inl i) j = matrixOf T i j := rfl
  have e0 (i : n) (j : m) : matrixOf V (Sum.inr i) j = 0 := by simp [V,paste]
  have top : J.toBlocks₁₁ + J.toBlocks₁₂ * matrixOf G = matrixOf T := by
    ext i j
    have h := congrFun (congrFun hm (Sum.inl i)) j
    simp only [Matrix.mul_apply,Fintype.sum_sum_type,eu,ew,ev] at h
    simpa [Matrix.mul_apply, Matrix.toBlocks₁₁,Matrix.toBlocks₁₂] using h
  have bot : J.toBlocks₂₁ + J.toBlocks₂₂ * matrixOf G = 0 := by
    ext i j
    have h := congrFun (congrFun hm (Sum.inr i)) j
    simp only [Matrix.mul_apply,Fintype.sum_sum_type,eu,ew,e0] at h
    simpa [Matrix.mul_apply, Matrix.toBlocks₂₁,Matrix.toBlocks₂₂] using h
  have hd : J.toBlocks₂₂.det ≠ 0 := by simpa using hfast 0 (by simp)
  have hb : J.toBlocks₂₂ * matrixOf G = -J.toBlocks₂₁ := (eq_neg_of_add_eq_zero_right bot)
  have hG := congrArg (fun Q => J.toBlocks₂₂⁻¹ * Q) hb
  dsimp only at hG
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hd), Matrix.mul_neg] at hG
  change J.toBlocks₁₁ - J.toBlocks₁₂ * J.toBlocks₂₂⁻¹ * J.toBlocks₂₁ = matrixOf T
  rw [hG, Matrix.mul_neg, ← Matrix.mul_assoc, ← sub_eq_add_neg] at top
  exact top

#print axioms schur_on_graph
end ERK.Lift
