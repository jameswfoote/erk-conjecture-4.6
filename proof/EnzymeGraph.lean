import Model
import FirstLift
import FastSpectrum
import Lift
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp

/-! Smooth eta perturbation of the two enzyme blocks at fixed positive delta. -/
noncomputable section
open Filter Matrix
open scoped Topology
namespace ERK.Second
open Model

def normalized (s δ : ℝ) (tx : ℝ × (I → ℝ)) : State :=
  let w := tx.2 ∘ Sum.inr
  let u := toSlow δ (tx.2 ∘ Sum.inl)
  scaledState 1 (classA tx.1 u w) (u 0) (u 1) (u 2) (freeE w) (freeF s w) w

theorem normalized_continuous (s δ : ℝ) : Continuous (normalized s δ) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [normalized,scaledState,classA,freeE,freeF,toSlow] <;> fun_prop

theorem eta_smooth (p q K δ s : ℝ) : ContDiff ℝ 1 (etaEq p q K δ s) := by
  apply contDiff_pi.mpr
  rintro ((i|i)|i) <;> fin_cases i <;>
    dsimp [etaEq,fromSlow,substrateRHS,enzymeRHS,classA,freeE,freeF,toSlow] <;> fun_prop

theorem den_positive {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) (y : M → ℝ)
    (hA : 0 < freeA (toSlow δ y)) (hy : ∀ i, 0 < y i) :
    0 < eDen K δ (freeA (toSlow δ y)) (toSlow δ y 1) (toSlow δ y 2) ∧
    0 < fDen K δ (toSlow δ y 0) (toSlow δ y 1) := by
  have hB := hy (.inl 0)
  have hC := mul_pos hδ (hy (.inr 0))
  have hD := mul_pos hδ (hy (.inr 1))
  constructor <;> dsimp [eDen,fDen,toSlow] at * <;> positivity

theorem positive_seed {K δ s : ℝ} (hK : 0 < K) (hδ : 0 < δ) (hs : 0 < s) (y : M → ℝ)
    (hA : 0 < freeA (toSlow δ y)) (hy : ∀ i, 0 < y i) :
    ∀ i, 0 < normalized s δ (0,graphPoint K δ s y) i := by
  let u := toSlow δ y
  let w := boundGraph K δ s u
  have hB : 0 < u 0 := hy (.inl 0)
  have hC : 0 < u 1 := mul_pos hδ (hy (.inr 0))
  have hD : 0 < u 2 := mul_pos hδ (hy (.inr 1))
  have hden := den_positive hK hδ y hA hy
  have hfree : freeE w = graphE K δ u ∧ freeF s w = graphF K δ s u :=
    enzymeGraph_free hden.1.ne' hden.2.ne'
  have pos := enzymeGraph_positive hK hδ hA hB hC hD hs
  have he : 0 < freeE w := hfree.1.symm ▸ pos.1
  have hf : 0 < freeF s w := hfree.2.symm ▸ pos.2.1
  have hw : ∀ i, 0 < w i := pos.2.2
  have ha : 0 < classA 0 u w := by simpa [classA,freeA] using hA
  change ∀ i, 0 < scaledState 1 (classA 0 u w) (u 0) (u 1) (u 2) (freeE w) (freeF s w) w i
  intro i
  fin_cases i <;> dsimp [scaledState] <;> (try simp only [one_mul]) <;> first | assumption | exact hw _

theorem eDen_cont (K δ : ℝ) :
    Continuous (fun y : M → ℝ => eDen K δ (freeA (toSlow δ y)) (toSlow δ y 1) (toSlow δ y 2)) := by
  dsimp [eDen,freeA,toSlow]
  fun_prop

theorem fDen_cont (K δ : ℝ) :
    Continuous (fun y : M → ℝ => fDen K δ (toSlow δ y 0) (toSlow δ y 1)) := by
  dsimp [fDen,toSlow]
  fun_prop

theorem graph_local {p q K δ s : ℝ} (hK : 0 < K) (hδ : 0 < δ) (y : M → ℝ)
    (hA : 0 < freeA (toSlow δ y)) (hy : ∀ i, 0 < y i) :
    ∀ᶠ v in 𝓝 y, etaEq p q K δ s (0,graphPoint K δ s v) = Sum.elim (scaledReduced p q K δ s v) 0 := by
  have h := den_positive hK hδ y hA hy
  filter_upwards [(eDen_cont K δ).continuousAt.eventually_ne h.1.ne',
    (fDen_cont K δ).continuousAt.eventually_ne h.2.ne'] with z he hf
  exact etaEq_on_graph hδ.ne' z he hf

set_option maxHeartbeats 800000 in
theorem graph_smooth {K δ s : ℝ} (hK : 0 < K) (hδ : 0 < δ) (y : M → ℝ)
    (hA : 0 < freeA (toSlow δ y)) (hy : ∀ i, 0 < y i) :
    ContDiffAt ℝ 1 (fun v => boundGraph K δ s (toSlow δ v)) y := by
  have h := den_positive hK hδ y hA hy
  have hE := h.1.ne'
  have hF := h.2.ne'
  dsimp [eDen,fDen,freeA,toSlow] at hE hF
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;>
    dsimp [boundGraph,enzymeGraph,graphE,graphF,eDen,fDen,freeA,toSlow] <;>
    fun_prop (disch := first | assumption | positivity)


theorem scaledReduced_eq_first {p q K δ s : ℝ} (hδ : δ ≠ 0) :
    scaledReduced p q K δ s = First.dynamics p q K s δ := by
  funext y
  have ha : freeA (toSlow δ y) = First.remaining δ y := by dsimp [freeA,toSlow,First.remaining]; ring
  have he : graphE K δ (toSlow δ y) = First.freeE K δ y := by
    unfold graphE First.freeE
    rw [ha]
    rfl
  have hf : graphF K δ s (toSlow δ y) = First.freeF K s δ y := rfl
  unfold scaledReduced
  rw [enzymeReduced_scaled hδ y]
  rw [ha,he,hf]
  rfl

end ERK.Second
