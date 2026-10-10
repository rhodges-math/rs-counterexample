import RSCounterexample.FlagVarieties.Foundations.Schemes.ProjectiveLine

/-! # Homogeneous evaluation under a common scalar change -/

noncomputable section

namespace FlagVarieties.Foundations.ProjectiveLine

variable {R S : Type*} [CommRing R] [CommRing S]

theorem evaluation_scale_of_homogeneous (φ : R →+* S) (δ ε c : S)
    {p : MvPolynomial (Fin 2) R} {n : ℕ} (hp : p.IsHomogeneous n) :
    evaluation φ (c * δ) (c * ε) p = c ^ n * evaluation φ δ ε p := by
  classical
  change p.eval₂ φ ![c * δ, c * ε] = c ^ n * p.eval₂ φ ![δ, ε]
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdg : d 0 + d 1 = n := by
    have hg : d.degree = n := by
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
      exact hp (MvPolynomial.mem_support_iff.mp hd)
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hg
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow]
  rw [← hdg, pow_add]
  ring

theorem isCoprime_unit_scale (δ ε : S) (h : IsCoprime δ ε) (u : Sˣ) :
    IsCoprime ((u : S) * δ) ((u : S) * ε) := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨a * (↑u⁻¹ : S), b * (↑u⁻¹ : S), ?_⟩
  calc
    a * (↑u⁻¹ : S) * ((u : S) * δ) + b * (↑u⁻¹ : S) * ((u : S) * ε) =
        a * ((↑u⁻¹ : S) * (u : S)) * δ + b * ((↑u⁻¹ : S) * (u : S)) * ε := by ring
    _ = 1 := by simpa using hab

end FlagVarieties.Foundations.ProjectiveLine
