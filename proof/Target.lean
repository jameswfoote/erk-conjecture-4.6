import Model
import Transport

noncomputable section

open Filter Set
open scoped Topology
namespace ERK.Target
open Model

/-- Exponential stability on a positive stoichiometric class in the spectral
sense of Conradi et al., §2.1. Derivatives are taken in nine independent
coordinates, after eliminating the three conserved totals. -/
def PositiveClassSink (k : Rates) (T : Totals) (x : State) : Prop :=
  (∀ i, 0 < x i) ∧ totals x = T ∧ rhs k x = 0 ∧
    Singular.Hurwitz (Transport.mat (fderiv ℝ (Model.field k T) (project x)))

/-- The target includes a single shared rate vector and a single shared class. -/
def BistabilityAt (p q : ℝ) : Prop :=
  ∃ k : Rates, ∃ T : Totals, (∀ i, 0 < k i) ∧ (∀ i, 0 < T i) ∧
    kinaseProcessivity k = p ∧ phosphataseProcessivity k = q ∧
    ∃ x y : State, x ≠ y ∧ PositiveClassSink k T x ∧ PositiveClassSink k T y

def Conjecture46 : Prop := ∀ p q : ℝ, 0 < p → p < 1 → 0 < q → q < 1 → BistabilityAt p q

theorem project_physical (s δ η : ℝ) (x : I → ℝ) :
    project (physicalMap s δ η x) = chartMap δ η x := by
  rw [← lift_chartMap, project_lift]

theorem etaDynamics_differentiable (p q K δ s η : ℝ) (x : I → ℝ) :
    DifferentiableAt ℝ (etaDynamics p q K δ s η) x := by
  apply differentiableAt_pi.mpr
  intro i
  rcases i with (i|i)|i <;> fin_cases i <;>
    dsimp [etaDynamics, etaEq, fromSlow, toSlow, substrateRHS, enzymeRHS, classA, freeE, freeF]
    <;> fun_prop

theorem sink_of_scaled {p q K δ η s : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (x : I → ℝ) (hx : ∀ i, 0 < physicalMap s δ η x i)
    (hz : etaDynamics p q K δ s η x = 0)
    (hH : Singular.Hurwitz (Transport.mat (fderiv ℝ (etaDynamics p q K δ s η) x))) :
    PositiveClassSink (prescribedRates p q K δ) ![1,η,η*s] (physicalMap s δ η x) := by
  let E := chartEquiv hδ.ne' hη.ne'
  have heq := eta_conjugacy (p:=p) (q:=q) (K:=K) (s:=s) hδ.ne' hη.ne'
  have hphys : Model.field (prescribedRates p q K δ) ![1,η,η*s] (chartMap δ η x) = 0 := by
    rw [heq, hz]
    change η • E 0 = 0
    simp
  refine ⟨hx, ?_, ?_, ?_⟩
  · rw [← lift_chartMap, totals_lift]
  · rw [← lift_chartMap]
    exact (equilibrium_iff _ _ _).mp hphys
  · rw [project_physical]
    exact Transport.change_of_coordinates E _ _ x η hη
      (etaDynamics_differentiable _ _ _ _ _ _ _) heq hH

theorem shared_witness {p q K δ η s : ℝ}
    (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hK : 0 < K) (hδ : 0 < δ) (hη : 0 < η) (hs : 0 < s)
    (u v : I → ℝ) (huv : u ≠ v)
    (hu : ∀ i, 0 < physicalMap s δ η u i) (hv : ∀ i, 0 < physicalMap s δ η v i)
    (zu : etaDynamics p q K δ s η u = 0) (zv : etaDynamics p q K δ s η v = 0)
    (su : Singular.Hurwitz (Transport.mat (fderiv ℝ (etaDynamics p q K δ s η) u)))
    (sv : Singular.Hurwitz (Transport.mat (fderiv ℝ (etaDynamics p q K δ s η) v))) :
    BistabilityAt p q := by
  obtain ⟨hk,hl⟩ := prescribed_processivities (p := p) (q := q) (K := K) hδ
  refine ⟨_, ![1,η,η*s], prescribedRates_pos hp hp' hq hq' hK hδ, ?_, hk, hl,
    physicalMap s δ η u, physicalMap s δ η v, ?_,
    sink_of_scaled hδ hη u hu zu su, sink_of_scaled hδ hη v hv zv sv⟩
  · intro i
    fin_cases i <;> dsimp <;> positivity
  · intro he
    apply huv
    apply (chartEquiv hδ.ne' hη.ne').injective
    simpa only [chartEquiv_apply,project_physical] using congrArg project he

#print axioms sink_of_scaled
#print axioms shared_witness
end ERK.Target
