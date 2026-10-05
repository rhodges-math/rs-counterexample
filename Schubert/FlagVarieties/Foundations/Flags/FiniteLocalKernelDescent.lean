import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Descent of finitely many compatible localized submodules

A finite family of local kernels descends by intersecting its inverse
images. The compatibility required here is the explicit denominator-clearing
condition; applications must derive it from their overlap equations.
No finite generation of the kernels or reducedness of the rings is needed.
-/

namespace FlagVarieties.Foundations.QuotientCharts

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

/-- Clearing a power of the inverted element suffices for inclusion after localization. -/
theorem localized_submodule_le_of_pow_smul_mem
    (a : A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization.Away a B]
    {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (f : M →ₗ[A] N) [IsLocalizedModule.Away a f]
    (P Q : Submodule A M)
    (h : ∀ m ∈ P, ∃ k : ℕ, a ^ k • m ∈ Q) :
    P.localized' B (.powers a) f ≤ Q.localized' B (.powers a) f := by
  rw [Submodule.localized'_eq_span, Submodule.span_le]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨k, hk⟩ := h m hm
  refine ⟨a ^ k • m, hk, ⟨a ^ k, ⟨k, rfl⟩⟩, ?_⟩
  exact IsLocalizedModule.mk'_cancel (S := .powers a) f m ⟨a ^ k, ⟨k, rfl⟩⟩

/-- Localization preserves the finite intersection used in kernel descent. -/
theorem localized_submodule_iInf_finite
    (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]
    {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (f : M →ₗ[A] N) [IsLocalizedModule S f]
    {I : Type*} [Fintype I] (P : I → Submodule A M) :
    (⨅ i, P i).localized' B S f = ⨅ i, (P i).localized' B S f := by
  classical
  simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Function.comp_apply,
    Submodule.IsLocalizedModule.localized'FrameHom_apply] using
    map_finset_inf (Submodule.localized'FrameHom B S f) Finset.univ P

/-- The intersection of inverse images has precisely the prescribed local kernels.
The explicit power condition is derived from overlap compatibility in
`Schemes/SelectedMorphismKernelDescent.lean`. -/
theorem finite_local_kernels_descend
    {I : Type*} [Fintype I] (s : I → A)
    (B : I → Type*) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    [∀ i, IsLocalization.Away (s i) (B i)]
    (N : I → Type*) [∀ i, AddCommGroup (N i)] [∀ i, Module A (N i)]
    [∀ i, Module (B i) (N i)] [∀ i, IsScalarTower A (B i) (N i)]
    (f : ∀ i, M →ₗ[A] N i) [∀ i, IsLocalizedModule.Away (s i) (f i)]
    (P : ∀ i, Submodule (B i) (N i))
    (h : ∀ i j m, f i m ∈ P i → ∃ k : ℕ, f j (s i ^ k • m) ∈ P j)
    (i : I) :
    (⨅ j, ((P j).restrictScalars A).comap (f j)).localized' (B i) (.powers (s i)) (f i) =
      P i := by
  let Q (j : I) : Submodule A M := ((P j).restrictScalars A).comap (f j)
  have hself : (Q i).localized' (B i) (.powers (s i)) (f i) = P i :=
    (Submodule.localized'gi (B i) (.powers (s i)) (f i)).l_u_eq (P i)
  change (⨅ j, Q j).localized' (B i) (.powers (s i)) (f i) = P i
  rw [localized_submodule_iInf_finite]
  apply le_antisymm
  · exact (iInf_le _ i).trans_eq hself
  · apply le_iInf
    intro j
    rw [← hself]
    exact localized_submodule_le_of_pow_smul_mem (s i) (B i) (f i) (Q i) (Q j)
      (fun m hm => h i j m hm)

end FlagVarieties.Foundations.QuotientCharts
