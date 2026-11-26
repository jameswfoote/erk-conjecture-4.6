import Target
import PhysicalPositive

noncomputable section
open Filter Set
open scoped Topology
namespace ERK
open Model

private theorem positive_near {s δ : ℝ} (u : ℝ → I → ℝ) (hc : ContinuousAt u 0)
    (hp : ∀ i, 0 < Second.normalized s δ (0,u 0) i) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, 0 < Second.normalized s δ (t,u t) i := by
  apply Filter.eventually_all.mpr
  intro i
  have h : ContinuousAt (fun t : ℝ => Second.normalized s δ (t,u t) i) 0 :=
    ((continuous_apply i).comp (Second.normalized_continuous s δ)).continuousAt.comp
      (continuousAt_id.prodMk hc)
  exact h.tendsto.eventually (Ioi_mem_nhds (hp i))

/-- Simultaneity of the last lift, including positivity of all reconstructed species. -/
theorem common_enzyme_parameter {p q K δ s : ℝ}
    (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hK : 0 < K) (hδ : 0 < δ) (hs : 0 < s)
    (u v : ℝ → I → ℝ) (huc : ContinuousAt u 0) (hvc : ContinuousAt v 0)
    (hsep : u 0 ≠ v 0)
    (hu : ∀ i, 0 < Second.normalized s δ (0,u 0) i)
    (hv : ∀ i, 0 < Second.normalized s δ (0,v 0) i)
    (hU : ∀ᶠ η in 𝓝[>] (0:ℝ), etaDynamics p q K δ s η (u η) = 0 ∧
      Singular.Hurwitz (Transport.mat (fderiv ℝ (etaDynamics p q K δ s η) (u η))))
    (hV : ∀ᶠ η in 𝓝[>] (0:ℝ), etaDynamics p q K δ s η (v η) = 0 ∧
      Singular.Hurwitz (Transport.mat (fderiv ℝ (etaDynamics p q K δ s η) (v η)))) :
    Target.BistabilityAt p q := by
  have hne : ∀ᶠ t in 𝓝 (0:ℝ), u t ≠ v t :=
    (huc.prodMk hvc).tendsto.eventually
      ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds hsep)
  have eventually_solved : ∀ᶠ η in 𝓝[>] (0:ℝ), Target.BistabilityAt p q := by
    filter_upwards [self_mem_nhdsWithin, hU, hV, hne.filter_mono nhdsWithin_le_nhds,
      (positive_near u huc hu).filter_mono nhdsWithin_le_nhds,
      (positive_near v hvc hv).filter_mono nhdsWithin_le_nhds] with η hη eu ev huv pu pv
    exact Target.shared_witness hp hp' hq hq' hK hδ hη hs _ _ huv
      (Second.physical_positive hη _ pu) (Second.physical_positive hη _ pv)
      eu.1 ev.1 eu.2 ev.2
  exact eventually_solved.exists.choose_spec

#print axioms common_enzyme_parameter

end ERK
