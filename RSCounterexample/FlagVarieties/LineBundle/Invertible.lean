import RSCounterexample.FlagVarieties.LineBundle.Minors
import TauCeti.AlgebraicGeometry.LineBundle.Pullback

/-!
# `𝓛(η)` is invertible

On the big cell of `v`, the sheaf `𝓛(η)` is free of rank one, with basis the section given by the
semi-invariant unit `τ_η = ∏ᵢ (m_i / m_{i+1})^{ηᵢ}` (`FlagVarieties.lineBundleTrivialization`).
Hence `𝓛(η)` is an invertible sheaf (`FlagVarieties.isInvertible_lineBundle`).
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

variable (R : Type u) [CommRing R] (n : ℕ) (η : Fin n → ℤ)

theorem exists_lineBundleBigCellSection (v : Equiv.Perm (Fin n)) :
    ∃ s : Γ(lineBundle R n η, bigCell R v), ((lineBundleι R n η).app (bigCell R v)).hom s =
      ((bigCellTwistUnit R v η : (Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v))ˣ) :
        Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v)) :=
  ((glBorelAction R n).mem_range_semiInvariantι_app_iff η (bigCell R v) _).mpr
    (isSemiInvariant_bigCellTwistUnit v η)

/-- The section of `𝓛(η)` over the big cell of `v` given by `τ_η`. -/
def lineBundleBigCellSection (v : Equiv.Perm (Fin n)) : Γ(lineBundle R n η, bigCell R v) :=
  Classical.choose (exists_lineBundleBigCellSection R n η v)

theorem lineBundleι_bigCellSection (v : Equiv.Perm (Fin n)) :
    ((lineBundleι R n η).app (bigCell R v)).hom (lineBundleBigCellSection R n η v) =
      ((bigCellTwistUnit R v η : (Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v))ˣ) :
        Γ(GLScheme R n, FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v)) :=
  Classical.choose_spec (exists_lineBundleBigCellSection R n η v)

/-- On the big cell, every section of `𝓛(η)` is uniquely a multiple of the basis section. -/
theorem bijective_smul_lineBundleBigCellSection (v : Equiv.Perm (Fin n))
    {W : (FlagScheme R n).Opens}
    (hW : W ≤ bigCell R v) :
    Function.Bijective (fun a : Γ(FlagScheme R n, W) =>
      a • ((lineBundle R n η).presheaf.map (homOfLE hW).op).hom
        (lineBundleBigCellSection R n η v)) :=
  (bigCellLocalData R v).bijective_smul_section_of_isUnit η hW (lineBundleBigCellSection R n η v)
    (by
      have hu := Units.isUnit (bigCellTwistUnit R v η)
      rw [← lineBundleι_bigCellSection] at hu
      exact hu)

/-- **The trivialization of `𝓛(η)` over the big cell of `v`.** -/
def lineBundleTrivialization (v : Equiv.Perm (Fin n)) :
    unitModule (bigCell R v).toScheme ≅ (lineBundle R n η).restrict (bigCell R v).ι :=
  have : IsIso (unitHomOfSection ((lineBundle R n η).restrict (bigCell R v).ι)
      (((lineBundle R n η).presheaf.map
        (homOfLE (Scheme.Opens.ι_image_le (bigCell R v) ⊤)).op).hom
          (lineBundleBigCellSection R n η v))) := by
    apply isIso_unitHomOfSection
    intro W'
    have hW : (bigCell R v).ι ''ᵁ W' ≤ bigCell R v := Scheme.Opens.ι_image_le _ W'
    have e : (fun a : Γ((bigCell R v).toScheme, W') =>
        a • (((lineBundle R n η).restrict (bigCell R v).ι).presheaf.map
          (homOfLE le_top : W' ⟶ ⊤).op).hom (((lineBundle R n η).presheaf.map
            (homOfLE (Scheme.Opens.ι_image_le (bigCell R v) ⊤)).op).hom
              (lineBundleBigCellSection R n η v))) =
        (fun a : Γ(FlagScheme R n, (bigCell R v).ι ''ᵁ W') =>
          a • ((lineBundle R n η).presheaf.map (homOfLE hW).op).hom
            (lineBundleBigCellSection R n η v)) := by
      have e1 : ((lineBundle R n η).presheaf.map
          ((bigCell R v).ι.opensFunctor.map (homOfLE le_top : W' ⟶ ⊤)).op).hom
            (((lineBundle R n η).presheaf.map
              (homOfLE (Scheme.Opens.ι_image_le (bigCell R v) ⊤)).op).hom
                (lineBundleBigCellSection R n η v)) =
          ((lineBundle R n η).presheaf.map (homOfLE hW).op).hom
            (lineBundleBigCellSection R n η v) := by
        rw [← AddMonoidHom.comp_apply, ← AddCommGrpCat.hom_comp, ← Functor.map_comp]
        rfl
      funext a
      change ((lineBundle R n η).smul (((bigCell R v).ι.appIso W').inv.hom a)).hom
          (((lineBundle R n η).presheaf.map
            ((bigCell R v).ι.opensFunctor.map (homOfLE le_top : W' ⟶ ⊤)).op).hom
              (((lineBundle R n η).presheaf.map
                (homOfLE (Scheme.Opens.ι_image_le (bigCell R v) ⊤)).op).hom
                  (lineBundleBigCellSection R n η v))) =
        ((lineBundle R n η).smul a).hom
          (((lineBundle R n η).presheaf.map (homOfLE hW).op).hom
            (lineBundleBigCellSection R n η v))
      rw [e1, Scheme.Opens.ι_appIso]
      rfl
    rw [e]
    exact bijective_smul_lineBundleBigCellSection R n η v hW
  asIso (unitHomOfSection ((lineBundle R n η).restrict (bigCell R v).ι)
    (((lineBundle R n η).presheaf.map
      (homOfLE (Scheme.Opens.ι_image_le (bigCell R v) ⊤)).op).hom
        (lineBundleBigCellSection R n η v)))

/-- **`𝓛(η)` is an invertible sheaf.** -/
theorem isInvertible_lineBundle :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible (FlagScheme R n) (lineBundle R n η) := by
  refine TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
    ⟨ULift.{u} (Equiv.Perm (Fin n)), fun v => bigCell R v.down, ?_,
      fun v => ⟨lineBundleTrivialization R n η v.down⟩⟩
  rw [TopologicalSpace.IsOpenCover, eq_top_iff]
  intro x _
  obtain ⟨v, hv⟩ := exists_mem_bigCell R x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨v⟩, hv⟩

end FlagVarieties
