import EnzymeGraph

noncomputable section
namespace ERK.Second
open Model

private theorem positive_cons {n : ℕ} (a : ℝ) (t : Fin n → ℝ) :
    (∀ i, 0 < Matrix.vecCons a t i) ↔ 0 < a ∧ ∀ j, 0 < t j := by
  rw [Fin.forall_fin_succ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- At positive total enzyme, undoing the normalization preserves all twelve strict inequalities. -/
private theorem scaled_positive_transfer {η A B C D e f : ℝ} (hη : 0 < η) (w : Bound)
    (hx : ∀ i, 0 < scaledState 1 A B C D e f w i) :
    ∀ i, 0 < scaledState η A B C D e f w i := by
  simp only [scaledState, positive_cons, one_mul] at hx ⊢
  obtain ⟨ha,he,hf,h3,h4,h5,h1,h2,hC,hD,h0,hB,hempty⟩ := hx
  exact ⟨ha,mul_pos hη he,mul_pos hη hf,mul_pos hη h3,mul_pos hη h4,mul_pos hη h5,
    mul_pos hη h1,mul_pos hη h2,hC,hD,mul_pos hη h0,hB,hempty⟩

theorem physical_positive {s δ η : ℝ} (hη : 0 < η) (x : I → ℝ)
    (hx : ∀ i, 0 < normalized s δ (η,x) i) : ∀ i, 0 < physicalMap s δ η x i :=
  scaled_positive_transfer (A:=classA η (toSlow δ (x ∘ Sum.inl)) (x ∘ Sum.inr))
    (B:=toSlow δ (x ∘ Sum.inl) 0) (C:=toSlow δ (x ∘ Sum.inl) 1) (D:=toSlow δ (x ∘ Sum.inl) 2)
    (e:=freeE (x ∘ Sum.inr)) (f:=freeF s (x ∘ Sum.inr)) hη (x ∘ Sum.inr) hx

#print axioms physical_positive
end ERK.Second
