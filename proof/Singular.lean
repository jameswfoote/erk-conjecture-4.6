import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-! Stability of a matrix with fast and slow row blocks. The spectral parameter and its
fast rescaling are compactified independently in a closed complex half-disk. -/
noncomputable section

namespace ERK.Singular

open Complex Filter Matrix Set
open scoped Topology

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Absence of a characteristic root in the closed right half-plane. -/
def Hurwitz (A : Matrix m m ℂ) : Prop :=
  ∀ z : ℂ, 0 ≤ z.re → (A - z • (1 : Matrix m m ℂ)).det ≠ 0

private def hemi : Set ℂ := Metric.closedBall 0 1 ∩ {z | 0 ≤ z.re}
private def scale (z : ℂ) : ℂ := ((1 - ‖z‖ : ℝ) : ℂ)
private noncomputable def rad (z : ℂ) : ℂ := z / ((1 + ‖z‖ : ℝ) : ℂ)

private theorem compact_hemi : IsCompact hemi :=
  (isCompact_closedBall (0 : ℂ) 1).inter_right (isClosed_le continuous_const Complex.continuous_re)

private theorem norm_le_one {z : ℂ} (hz : z ∈ hemi) : ‖z‖ ≤ 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right] using hz.1

private theorem rad_facts (z : ℂ) (hz : 0 ≤ z.re) :
    rad z ∈ hemi ∧ scale (rad z) ≠ 0 ∧ rad z = scale (rad z) * z := by
  have hd : 0 < 1 + ‖z‖ := by positivity
  have hn : ‖rad z‖ = ‖z‖ / (1 + ‖z‖) := by
    rw [rad, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  have hs : scale (rad z) = (((1 + ‖z‖)⁻¹ : ℝ) : ℂ) := by
    unfold scale
    rw [hn]
    congr 1
    field_simp
    ring
  constructor
  · constructor
    · change rad z ∈ Metric.closedBall (0 : ℂ) 1
      simp [Metric.mem_closedBall, dist_zero_right, hn, div_le_one hd]
    · change 0 ≤ (rad z).re
      rw [rad, Complex.div_ofReal_re]
      exact div_nonneg hz hd.le
  rw [hs]
  constructor
  · exact_mod_cast (inv_ne_zero hd.ne')
  · simp [rad, div_eq_mul_inv, mul_comm]

private def pencil (A : Matrix m m ℂ) (z : ℂ) : Matrix m m ℂ :=
  scale z • A - z • 1

private theorem pencil_regular (A : Matrix m m ℂ) (hA : Hurwitz A) {z : ℂ} (hz : z ∈ hemi) :
    (pencil A z).det ≠ 0 := by
  by_cases h : scale z = 0
  · have hne : z ≠ 0 := by rintro rfl; simp [scale] at h
    simp [pencil, h, Matrix.det_neg, hne]
  · have hpos : 0 < 1 - ‖z‖ := by
      refine lt_of_le_of_ne (sub_nonneg.mpr (norm_le_one hz)) ?_
      intro he
      exact h (by simp [scale, ← he])
    have hreal : 0 ≤ (z / scale z).re := by
      rw [scale, Complex.div_ofReal_re]
      exact div_nonneg hz.2 hpos.le
    have heq : pencil A z = scale z • (A - (z / scale z) • (1 : Matrix m m ℂ)) := by
      rw [pencil, smul_sub, smul_smul, mul_div_cancel₀ _ h]
    rw [heq, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ h) (hA _ hreal)

private def blocks (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ) (z w : ℂ) :=
  Matrix.fromBlocks (pencil A z) (scale z • B) (scale w • C) (pencil D w)

/-- On the limiting compatibility relation, one of the two homogenized spectral
parameters is at infinity, or the fast spectral parameter is zero. -/
private theorem boundary_regular (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (hD : Hurwitz D) (hS : Hurwitz (A - B * D⁻¹ * C))
    {z w : ℂ} (hz : z ∈ hemi) (hw : w ∈ hemi) (hrel : scale z * w = 0) :
    (blocks A B C D z w).det ≠ 0 := by
  rcases mul_eq_zero.mp hrel with hinf | hw0
  · have hne : z ≠ 0 := by rintro rfl; simp [scale] at hinf
    simp only [blocks, hinf, zero_smul, Matrix.det_fromBlocks_zero₁₂]
    exact mul_ne_zero (by simp [pencil, hinf, Matrix.det_neg, hne]) (pencil_regular D hD hw)
  · subst w
    have hd : D.det ≠ 0 := by simpa using hD 0 (by simp)
    letI : Invertible D := (D.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hd)).invertible
    have h0 : scale 0 = 1 := by simp [scale]
    have hSchur : pencil A z - scale z • B * D⁻¹ * C = pencil (A - B * D⁻¹ * C) z := by
      simp only [pencil, smul_sub, Matrix.smul_mul]
      abel
    simp only [blocks, h0, one_smul, pencil, zero_smul, sub_zero]
    rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
    apply mul_ne_zero hd
    change (pencil A z - scale z • B * D⁻¹ * C).det ≠ 0
    rw [hSchur]
    exact pencil_regular _ hS hz


/-- The fast time parameter followed by the four unscaled Jacobian blocks, in row order. -/
abbrev Data (m n : Type*) :=
  ℝ × Matrix m m ℂ × Matrix m n ℂ × Matrix n m ℂ × Matrix n n ℂ

private def regularSet : Set (Data m n × (ℂ × ℂ)) :=
  {v | scale v.2.1 * v.2.2 ≠ (v.1.1 : ℂ) * scale v.2.2 * v.2.1 ∨
    (blocks v.1.2.1 v.1.2.2.1 v.1.2.2.2.1 v.1.2.2.2.2 v.2.1 v.2.2).det ≠ 0}

private theorem open_regularSet : IsOpen (regularSet (m := m) (n := n)) := by
  apply IsOpen.union
  · apply isOpen_compl_iff.mpr
    apply isClosed_eq <;> unfold scale <;> fun_prop
  · apply isOpen_compl_iff.mpr
    apply isClosed_eq
    · unfold blocks pencil scale
      fun_prop
    · exact continuous_const

private theorem eventually_regular (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (hD : Hurwitz D) (hS : Hurwitz (A - B * D⁻¹ * C)) :
    ∀ᶠ v : Data m n in 𝓝 (0,A,B,C,D),
      ∀ z ∈ hemi, ∀ w ∈ hemi, scale z * w = (v.1 : ℂ) * scale w * z →
        (blocks v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 z w).det ≠ 0 := by
  let x : Data m n := (0,A,B,C,D)
  have hsub : ({x} : Set (Data m n)) ×ˢ (hemi ×ˢ hemi) ⊆ regularSet := by
    rintro ⟨v, z, w⟩ ⟨hv, hz, hw⟩
    obtain rfl : v = x := hv
    change scale z * w ≠ (0 : ℝ) * scale w * z ∨ _
    simp only [Complex.ofReal_zero, zero_mul]
    exact or_iff_not_imp_left.mpr (fun H => boundary_regular A B C D hD hS hz hw (not_ne_iff.mp H))
  obtain ⟨U,V,hU,_,hx,hV,hUV⟩ := generalized_tube_lemma isCompact_singleton
    (compact_hemi.prod compact_hemi) open_regularSet hsub
  filter_upwards [hU.mem_nhds (hx (Set.mem_singleton x))] with v hv
  intro z hz w hw hzw
  exact (hUV ⟨hv, hV ⟨hz,hw⟩⟩ : (v,(z,w)) ∈ regularSet).resolve_left (not_not_intro hzw)

private theorem det_scaled_rows (a b : ℂ) (A : Matrix m m ℂ) (B : Matrix m n ℂ)
    (C : Matrix n m ℂ) (D : Matrix n n ℂ) :
    (fromBlocks (a • A) (a • B) (b • C) (b • D)).det =
    ((a ^ Fintype.card m) * b ^ Fintype.card n) * (fromBlocks A B C D).det := by
  have he : fromBlocks (a • A) (a • B) (b • C) (b • D) =
      fromBlocks (a • (1 : Matrix m m ℂ)) 0 0 (b • (1 : Matrix n n ℂ)) *
        fromBlocks A B C D := by
    simp [Matrix.fromBlocks_multiply, Matrix.smul_mul]
  rw [he, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- The dynamical Jacobian in slow time, with the lower block row divided by the fast time parameter. -/
def jacobian (v : Data m n) : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks v.2.1 v.2.2.1 ((v.1 : ℂ)⁻¹ • v.2.2.2.1) ((v.1 : ℂ)⁻¹ • v.2.2.2.2)

omit [Fintype m] [Fintype n] in
private theorem jac_shift (v : Data m n) (z : ℂ) :
    jacobian v - z • 1 = fromBlocks (v.2.1 - z • 1) v.2.2.1
      ((v.1 : ℂ)⁻¹ • v.2.2.2.1) ((v.1 : ℂ)⁻¹ • v.2.2.2.2 - z • 1) := by
  rw [← Matrix.fromBlocks_one (l := m) (m := n)]
  ext (i|i) (j|j) <;> simp [jacobian, Matrix.one_apply]

/-- If the frozen fast block and its slow Schur complement are Hurwitz, then every
sufficiently nearby block system with a positive fast time parameter is Hurwitz.
All four matrix blocks are allowed to vary with that parameter. -/
theorem eventually_hurwitz (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (hD : Hurwitz D) (hS : Hurwitz (A - B * D⁻¹ * C)) :
    ∀ᶠ v : Data m n in 𝓝 (0,A,B,C,D), 0 < v.1 → Hurwitz (jacobian v) := by
  filter_upwards [eventually_regular A B C D hD hS] with v hreg
  intro hpos ζ hζ
  let t : ℂ := (v.1 : ℂ)
  have htn : t ≠ 0 := by dsimp [t]; exact_mod_cast hpos.ne'
  have htζ : 0 ≤ (t * ζ).re := by simpa [t, Complex.mul_re] using mul_nonneg hpos.le hζ
  obtain ⟨hz,haz,hz'⟩ := rad_facts ζ hζ
  obtain ⟨hw,hbw,hw'⟩ := rad_facts (t*ζ) htζ
  let z := rad ζ
  let w := rad (t*ζ)
  let a := scale z
  let b := scale w
  have hza : z = a * ζ := hz'
  have hwb : w = b * (t * ζ) := hw'
  have hrel : a * w = t * b * z := by rw [hza, hwb]; ring
  have hdet := hreg z hz w hw hrel
  have hp : blocks v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 z w =
      fromBlocks (a • (v.2.1 - ζ • 1)) (a • v.2.2.1)
        ((b*t) • (t⁻¹ • v.2.2.2.1)) ((b*t) • (t⁻¹ • v.2.2.2.2 - ζ • 1)) := by
    unfold blocks pencil
    change fromBlocks (a • _ - z • 1) (a • _) (b • _) (b • _ - w • 1) = _
    rw [hza, hwb]
    simp [smul_sub, smul_smul, mul_assoc, htn]
  rw [hp, det_scaled_rows] at hdet
  rw [jac_shift]
  exact right_ne_zero_of_mul hdet


/-- Filter form of the spectral lifting theorem, for a family of four convergent blocks. -/
theorem hurwitz_of_tendsto {ι : Type*} {L : Filter ι}
    (ε : ι → ℝ) (A : ι → Matrix m m ℂ) (B : ι → Matrix m n ℂ)
    (C : ι → Matrix n m ℂ) (D : ι → Matrix n n ℂ)
    (A₀ : Matrix m m ℂ) (B₀ : Matrix m n ℂ) (C₀ : Matrix n m ℂ) (D₀ : Matrix n n ℂ)
    (hε : Tendsto ε L (𝓝 0)) (hpos : ∀ᶠ i in L, 0 < ε i)
    (hA : Tendsto A L (𝓝 A₀)) (hB : Tendsto B L (𝓝 B₀))
    (hC : Tendsto C L (𝓝 C₀)) (hD : Tendsto D L (𝓝 D₀)) (hfast : Hurwitz D₀)
    (hslow : Hurwitz (A₀ - B₀ * D₀⁻¹ * C₀)) :
    ∀ᶠ i in L, Hurwitz (jacobian (ε i, A i, B i, C i, D i)) := by
  have ht := hε.prodMk_nhds (hA.prodMk_nhds (hB.prodMk_nhds (hC.prodMk_nhds hD)))
  filter_upwards [ht.eventually (eventually_hurwitz A₀ B₀ C₀ D₀ hfast hslow), hpos] with i h hi
  exact h hi

/-- Changing from slow time to physical time multiplies all nonzero spectral
rates by a positive constant and preserves class-relative spectral stability. -/
theorem hurwitz_pos_smul (A : Matrix m m ℂ) (hA : Hurwitz A) (t : ℝ) (ht : 0 < t) :
    Hurwitz ((t : ℂ) • A) := by
  intro z hz
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hp : 0 ≤ (z / (t : ℂ)).re := by
    rw [Complex.div_ofReal_re]
    exact div_nonneg hz ht.le
  have he : (t : ℂ) • A - z • 1 = (t : ℂ) • (A - (z / (t : ℂ)) • 1) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ ht']
  rw [he, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ ht') (hA _ hp)

theorem hurwitz_iff (A : Matrix m m ℂ) : Hurwitz A ↔
    ∀ z : ℂ, (z • (1 : Matrix m m ℂ) - A).det = 0 → z.re < 0 := by
  have eqz (z : ℂ) : (z • (1 : Matrix m m ℂ) - A).det = 0 ↔ (A - z • 1).det = 0 := by
    rw [← neg_sub (z • (1 : Matrix m m ℂ)) A, Matrix.det_neg]
    simp
  constructor
  · intro h z hz
    exact lt_of_not_ge fun hge => h z hge ((eqz z).mp hz)
  · intro h z hge hz
    exact (not_lt_of_ge hge) (h z ((eqz z).mpr hz))

#print axioms eventually_hurwitz
#print axioms hurwitz_of_tendsto
end ERK.Singular
