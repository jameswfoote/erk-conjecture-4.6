import Common
import SecondLift

noncomputable section
open Filter Set
open scoped Topology
namespace ERK
open Model

/-- Conjecture 4.6, with shared kinetic and total parameters and class-relative stability. -/
theorem conjecture_4_6 (p q : ℝ) (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1) :
    ∃ k : Fin 13 → ℝ, ∃ T : Fin 3 → ℝ, (∀ i, 0 < k i) ∧ (∀ i, 0 < T i) ∧
      kinaseProcessivity k = p ∧ phosphataseProcessivity k = q ∧
      ∃ x y : Fin 12 → ℝ, x ≠ y ∧
        Target.PositiveClassSink k T x ∧ Target.PositiveClassSink k T y := by
  let s := (1+p)/(2*q)
  have hs : 0 < s := by dsimp [s]; positivity
  obtain ⟨K,hK,hsmall⟩ := First.two_sinks hp hp' hq hq'
  have pos_delta : ∀ᶠ δ in 𝓝[>] (0:ℝ), (0:ℝ) < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,ya,yb,hab,hy⟩ := (pos_delta.and hsmall).exists
  change 0 < δ at hδ
  have one (y : M → ℝ) (hmem : y ∈ ({ya,yb} : Set (M → ℝ))) :
      ∃ u : ℝ → I → ℝ, u 0 = graphPoint K δ s y ∧ ContinuousAt u 0 ∧
        (∀ i, 0 < Second.normalized s δ (0,u 0) i) ∧
        ∀ᶠ η in 𝓝[>] (0:ℝ), etaDynamics p q K δ s η (u η) = 0 ∧
          Singular.Hurwitz (Transport.mat (fderiv ℝ (etaDynamics p q K δ s η) (u η))) := by
    obtain ⟨hA, hpos, hz, hstab⟩ := hy y hmem
    have hrem : freeA (toSlow δ y) = First.remaining δ y := by
      dsimp [freeA,toSlow,First.remaining]
      ring
    have hA' := hrem.symm ▸ hA
    have field_eq := Second.scaledReduced_eq_first (p:=p) (q:=q) (K:=K) (s:=s) hδ.ne'
    have hz' : scaledReduced p q K δ s y = 0 := by rw [field_eq]; exact hz
    have hstab' : Singular.Hurwitz (Lift.matrixOf (fderiv ℝ (scaledReduced p q K δ s) y)) := by
      rw [field_eq]; exact hstab
    obtain ⟨u,hu,huc,huv⟩ := Second.eta_sink_branch hK hδ y hA' hpos hz' hstab'
    refine ⟨u,hu,huc,?_,?_⟩
    · rw [hu]
      exact Second.positive_seed hK hδ hs y hA' hpos
    · exact huv.mono fun _ h => h.2
  obtain ⟨u,hu,huc,hup,hus⟩ := one ya (by simp)
  obtain ⟨v,hv,hvc,hvp,hvs⟩ := one yb (by simp)
  have hsep : u 0 ≠ v 0 := by
    rw [hu,hv]
    intro h
    exact hab.ne (congrFun h (.inl (.inl 0)))
  exact common_enzyme_parameter hp hp' hq hq' hK hδ hs u v huc hvc hsep hup hvp hus hvs

#print axioms conjecture_4_6

end ERK
