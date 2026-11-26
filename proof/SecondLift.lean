import EnzymeGraph
import EnzymeBlock
import Lift

noncomputable section
open Filter Matrix
open scoped Topology
namespace ERK.Second
open Model

private theorem basis_insert (j : Fin 6) : insertFast (Pi.single j 1) = Pi.single (.inr j) 1 := by
  funext i
  cases i <;> simp [insertFast,Pi.single_apply]

theorem fast_block (p q K δ s : ℝ) (x : I → ℝ) :
    (Lift.stateMatrix (etaEq p q K δ s) (0,x)).toBlocks₂₂ =
      (atFastMatrix K δ x).map Complex.ofReal := by
  ext i j
  simp only [Lift.stateMatrix, Matrix.toBlocks₂₂, Lift.matrixOf_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, Matrix.map_apply]
  have h := congrFun (fast_fderiv p q K δ s x (Pi.single j 1)
    (eta_smooth p q K δ s).contDiffAt.differentiableAt_one) i
  rw [basis_insert] at h
  rw [Matrix.mulVec_single_one] at h
  exact congrArg Complex.ofReal h

private theorem neg_pencil {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (h : ∀ z : ℂ, (z • 1 - A).det = 0 → z.re < 0) : Singular.Hurwitz A := by
  intro z hz he
  have hn : (z • 1 - A) = -(A-z • 1) := by abel
  exact (not_lt_of_ge hz) (h z (by rw [hn,Matrix.det_neg,he]; simp))

private theorem six_stable {K δ A B C D : ℝ} (hK : 0 < K) (hδ : 0 < δ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hD : 0 < D) :
    Singular.Hurwitz ((fastMatrix K δ A B C D).map Complex.ofReal) := by
  obtain ⟨h₁, h₂⟩ := Fast.both_enzyme_blocks A B C D K δ hA hB hC hD hK hδ
  let X := Fast.enzyme (K*A) (C/δ) (D/δ) (1/δ)
  let Y := Fast.enzyme (K*B) 0 (C/δ) (1/δ)
  let e : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv
  intro z hz
  have hmat : Matrix.reindex e.symm e.symm ((fastMatrix K δ A B C D).map Complex.ofReal - z • 1) =
      Matrix.fromBlocks (X-z • 1) 0 0 (Y-z • 1) := by
    have ix0 : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) (Sum.inl 0) = 0 := rfl
    have ix1 : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) (Sum.inl 1) = 1 := rfl
    have ix2 : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) (Sum.inl 2) = 2 := rfl
    have ix3 : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) (Sum.inr 0) = 3 := rfl
    have ix4 : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) (Sum.inr 1) = 4 := rfl
    have ix5 : (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6) (Sum.inr 2) = 5 := rfl
    ext (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;>
      simp [e,X,Y,Matrix.reindex_apply,fastMatrix,Fast.enzyme,Matrix.fromBlocks,ix0,ix1,ix2,ix3,ix4,ix5]
  rw [← Matrix.det_reindex_self e.symm, hmat, Matrix.det_fromBlocks_zero₂₁]
  exact mul_ne_zero (neg_pencil h₁ z hz) (neg_pencil h₂ z hz)

theorem graph_fast_stable {p q K δ s : ℝ} (hK : 0 < K) (hδ : 0 < δ) (y : M → ℝ)
    (hA : 0 < freeA (toSlow δ y)) (hy : ∀ i, 0 < y i) :
    Singular.Hurwitz (Lift.stateMatrix (etaEq p q K δ s) (0,graphPoint K δ s y)).toBlocks₂₂ := by
  rw [fast_block]
  exact six_stable hK hδ hA (hy (.inl 0)) (mul_pos hδ (hy (.inr 0))) (mul_pos hδ (hy (.inr 1)))

theorem lift_field_eq (p q K δ s η : ℝ) :
    Lift.field (etaEq p q K δ s) η = etaDynamics p q K δ s η := by
  funext x i
  cases i <;> simp [Lift.field,Lift.rowMap,etaDynamics,div_eq_mul_inv,mul_comm]

/-- Combine the two generic lift lemmas before specializing the coordinate dimension. -/
private theorem branch_on_graph {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : ℝ × Lift.Space m n → Lift.Space m n)
    (g : (m → ℝ) → n → ℝ) (R : (m → ℝ) → m → ℝ) (y : m → ℝ)
    (hc : ContDiffAt ℝ 1 H (0,Sum.elim y (g y))) (hg : DifferentiableAt ℝ g y)
    (hr : DifferentiableAt ℝ R y)
    (hgraph : ∀ᶠ v in 𝓝 y, H (0,Sum.elim v (g v)) = Sum.elim (R v) 0)
    (hfast : Singular.Hurwitz (Lift.stateMatrix H (0,Sum.elim y (g y))).toBlocks₂₂)
    (hz : R y = 0) (hs : Singular.Hurwitz (Lift.matrixOf (fderiv ℝ R y))) :
    ∃ u : ℝ → Lift.Space m n, u 0 = Sum.elim y (g y) ∧ ContinuousAt u 0 ∧
      ∀ᶠ t in 𝓝[>] (0:ℝ), H (t,u t) = 0 ∧ Lift.field H t (u t) = 0 ∧
        Singular.Hurwitz (Lift.matrixOf (fderiv ℝ (Lift.field H t) (u t))) := by
  have schur := Lift.schur_on_graph H g R y hc.differentiableAt_one hg hr hgraph hfast
  dsimp only at schur
  have hzero : H (0,Sum.elim y (g y)) = 0 := by
    rw [hgraph.self_of_nhds,hz]
    funext i
    cases i <;> rfl
  exact Lift.stable_branch H _ hzero hc hfast ((congrArg Singular.Hurwitz schur).mpr hs)

theorem eta_sink_branch {p q K δ s : ℝ} (hK : 0 < K) (hδ : 0 < δ)
    (y : M → ℝ) (hA : 0 < freeA (toSlow δ y)) (hy : ∀ i, 0 < y i)
    (hzero : scaledReduced p q K δ s y = 0)
    (hstable : Singular.Hurwitz (Lift.matrixOf (fderiv ℝ (scaledReduced p q K δ s) y))) :
    ∃ u : ℝ → I → ℝ, u 0 = graphPoint K δ s y ∧ ContinuousAt u 0 ∧
      ∀ᶠ η in 𝓝[>] (0:ℝ), etaEq p q K δ s (η,u η) = 0 ∧
        etaDynamics p q K δ s η (u η) = 0 ∧
        Singular.Hurwitz (Lift.matrixOf (fderiv ℝ (etaDynamics p q K δ s η) (u η))) := by
  let H := etaEq p q K δ s
  let g := fun v => boundGraph K δ s (toSlow δ v)
  let R := scaledReduced p q K δ s
  let x : Lift.Space M (Fin 6) := Sum.elim y (g y)
  let J := Lift.stateMatrix H (0,x)
  have hC : ContDiffAt ℝ 1 H (0,x) := (eta_smooth p q K δ s).contDiffAt
  have hfast := graph_fast_stable (p:=p) (q:=q) (s:=s) hK hδ y hA hy
  change Singular.Hurwitz J.toBlocks₂₂ at hfast
  have hg := graph_local (p:=p) (q:=q) (s:=s) hK hδ y hA hy
  have hR : DifferentiableAt ℝ R y := by
    have ha : freeA (toSlow δ y) = First.remaining δ y := by dsimp [freeA,toSlow,First.remaining]; ring
    change DifferentiableAt ℝ (scaledReduced p q K δ s) y
    rw [scaledReduced_eq_first hδ.ne']
    exact First.dynamics_diff hK hδ (ha ▸ hA) hy
  obtain ⟨u,hu,hc,hev⟩ := branch_on_graph (m := M) (n := Fin 6) H g R y hC
    (graph_smooth hK hδ y hA hy).differentiableAt_one hR hg hfast hzero hstable
  refine ⟨u,hu,hc,?_⟩
  filter_upwards [hev] with t ht
  simpa [H,lift_field_eq] using ht

#print axioms eta_sink_branch
end ERK.Second
