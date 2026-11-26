import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

noncomputable section

open Filter Set
open scoped Topology

namespace ERK.Lifting

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- A branch of zeros of the unscaled equilibrium constraints. -/
theorem equilibrium_branch (H : ℝ × X → X) (x : X) (hz : H (0,x) = 0)
    (M : ℝ →L[ℝ] X) (L : X ≃L[ℝ] X)
    (hd : HasStrictFDerivAt H
      ((L : X →L[ℝ] X).comp (ContinuousLinearMap.snd ℝ ℝ X) +
       M.comp (ContinuousLinearMap.fst ℝ ℝ X)) (0,x)) :
    ∃ u : ℝ → X, u 0 = x ∧ ContinuousAt u 0 ∧ ∀ᶠ t in 𝓝 0, H (t,u t) = 0 := by
  let f : ℝ × X → ℝ × X := fun z => (z.1, H z)
  let E := (ContinuousLinearEquiv.refl ℝ ℝ).skewProd L M
  have hd' : HasStrictFDerivAt f (E : (ℝ × X) →L[ℝ] (ℝ × X)) (0,x) := by
    convert (hasStrictFDerivAt_fst.prodMk hd) using 1
  have hfx : f (0,x) = (0,0) := by simp [f,hz]
  let inv := hd'.localInverse f E (0,x)
  have hinv : inv (0,0) = (0,x) := by rw [← hfx]; exact hd'.localInverse_apply_image
  have hline : Tendsto (fun t : ℝ => (t, (0 : X))) (𝓝 0) (𝓝 (f (0,x))) := by
    rw [hfx]
    exact tendsto_id.prodMk_nhds tendsto_const_nhds
  have hconv : Tendsto (fun t : ℝ => inv (t,0)) (𝓝 0) (𝓝 (0,x)) :=
    hd'.localInverse_tendsto.comp hline
  refine ⟨fun t => (inv (t,0)).2, congrArg Prod.snd hinv, ?_, ?_⟩
  · simpa only [ContinuousAt, hinv] using continuous_snd.continuousAt.tendsto.comp hconv
  · filter_upwards [hline.eventually hd'.eventually_right_inverse] with t ht
    change f (inv (t,0)) = (t,0) at ht
    have ht₁ : (inv (t,0)).1 = t := congrArg Prod.fst ht
    have ht₂ : H (inv (t,0)) = 0 := congrArg Prod.snd ht
    have heq : inv (t,0) = (t,(inv (t,0)).2) := Prod.ext ht₁ rfl
    exact (congrArg H heq).symm.trans ht₂

/-- Two distinct zeros persist at each common sufficiently small positive parameter.
The open sets can encode positivity in local class coordinates. -/
theorem two_equilibria (H : ℝ × X → X) (a b : X) (ha : H (0,a) = 0)
    (hb : H (0,b) = 0) (hab : a ≠ b) {U V : Set X}
    (hU : U ∈ 𝓝 a) (hV : V ∈ 𝓝 b)
    (M₁ M₂ : ℝ →L[ℝ] X) (L₁ L₂ : X ≃L[ℝ] X)
    (h₁ : HasStrictFDerivAt H ((L₁ : X →L[ℝ] X).comp (ContinuousLinearMap.snd ℝ ℝ X) +
       M₁.comp (ContinuousLinearMap.fst ℝ ℝ X)) (0,a))
    (h₂ : HasStrictFDerivAt H ((L₂ : X →L[ℝ] X).comp (ContinuousLinearMap.snd ℝ ℝ X) +
       M₂.comp (ContinuousLinearMap.fst ℝ ℝ X)) (0,b)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ x ∈ U, ∃ y ∈ V, x ≠ y ∧ H (t,x) = 0 ∧ H (t,y) = 0 := by
  obtain ⟨u, hu, huc, huz⟩ := equilibrium_branch H a ha M₁ L₁ h₁
  obtain ⟨v, hv, hvc, hvz⟩ := equilibrium_branch H b hb M₂ L₂ h₂
  have hune : ∀ᶠ t in 𝓝 (0 : ℝ), u t ≠ v t :=
    (huc.prodMk hvc).tendsto.eventually
      ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds (by simpa [hu,hv] using hab))
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [huz,hvz,hune,huc.tendsto.eventually (hu ▸ hU),hvc.tendsto.eventually (hv ▸ hV)]
    with t htu htv huv ut vt
  exact ⟨u t,ut,v t,vt,huv,htu,htv⟩

#print axioms equilibrium_branch
#print axioms two_equilibria


/-- The invertible derivative of the unscaled equilibrium equations, reconstructed
from its fast block and its slow Schur complement. -/
def schurEquiv (B : Y →L[ℝ] X) (C : X →L[ℝ] Y) (D : Y ≃L[ℝ] Y) (S : X ≃L[ℝ] X) :
    (X × Y) ≃L[ℝ] (X × Y) :=
  ((S.skewProd D C).trans (ContinuousLinearEquiv.prodComm ℝ X Y)).trans
    (((ContinuousLinearEquiv.refl ℝ Y).skewProd (ContinuousLinearEquiv.refl ℝ X)
      (B.comp (D.symm : Y →L[ℝ] Y))).trans (ContinuousLinearEquiv.prodComm ℝ Y X))

def blocks (A : X →L[ℝ] X) (B : Y →L[ℝ] X) (C : X →L[ℝ] Y) (D : Y →L[ℝ] Y) :
    (X × Y) →L[ℝ] (X × Y) :=
  ((A.comp (ContinuousLinearMap.fst ℝ X Y))+(B.comp (ContinuousLinearMap.snd ℝ X Y))).prod
    ((C.comp (ContinuousLinearMap.fst ℝ X Y))+(D.comp (ContinuousLinearMap.snd ℝ X Y)))

omit [CompleteSpace X] [CompleteSpace Y] in
theorem schurEquiv_eq (A : X →L[ℝ] X) (B : Y →L[ℝ] X) (C : X →L[ℝ] Y)
    (D : Y ≃L[ℝ] Y) (S : X ≃L[ℝ] X)
    (hs : ∀ y, S y = A y - B (D.symm (C y))) :
    (schurEquiv B C D S : (X × Y) →L[ℝ] (X × Y)) = blocks A B C (D : Y →L[ℝ] Y) := by
  apply ContinuousLinearMap.ext
  intro z
  rcases z with ⟨y,v⟩
  apply Prod.ext
  · simp [schurEquiv, blocks, ContinuousLinearEquiv.skewProd_apply, hs]
  · simp [schurEquiv, blocks, ContinuousLinearEquiv.skewProd_apply, add_comm]

theorem equilibrium_branch_schur (H : ℝ × (X × Y) → X × Y) (x : X × Y)
    (hz : H (0,x) = 0) (M : ℝ →L[ℝ] (X × Y))
    (A : X →L[ℝ] X) (B : Y →L[ℝ] X) (C : X →L[ℝ] Y)
    (D : Y ≃L[ℝ] Y) (S : X ≃L[ℝ] X) (hs : ∀ y, S y = A y - B (D.symm (C y)))
    (hd : HasStrictFDerivAt H ((blocks A B C (D : Y →L[ℝ] Y)).comp
      (ContinuousLinearMap.snd ℝ ℝ (X × Y)) + M.comp (ContinuousLinearMap.fst ℝ ℝ (X × Y))) (0,x)) :
    ∃ u : ℝ → X × Y, u 0 = x ∧ ContinuousAt u 0 ∧ ∀ᶠ t in 𝓝 0, H (t,u t) = 0 := by
  apply equilibrium_branch H x hz M (schurEquiv B C D S)
  rwa [schurEquiv_eq A B C D S hs]

#print axioms schurEquiv_eq
#print axioms equilibrium_branch_schur

end ERK.Lifting
