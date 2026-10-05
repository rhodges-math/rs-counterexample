import Schubert.RS.Geometric.Corollary
import Schubert.FlagVarieties.Modules.Geometric
import Schubert.FlagVarieties.Schubert.UnionPreimage

/-!
# Corollary 1.2 for the sheaf-theoretic modules

The statements of `Schubert.RS.Geometric.Corollary` for the sheaf-theoretic section modules
`H⁰(X, 𝓛(η)) = FlagVarieties.sections ℂ n I η` with the action of `B` of
`FlagVarieties.sectionsRep`:

* the geometric dual Joseph modules `P(ν) = H⁰(X_σ, 𝓛(η))` (`FlagVarieties.dualJoseph`)
  are rational, with `ch P(−u) = κ_u`;
* the tensor product `P(−a) ⊗ P(−b)` of the family (`Schubert.RS.Geometric.geometricFamilyTensor`)
  has character `κ_a κ_b`, and **admits no filtration whose layers are section modules
  `H⁰(X_S, 𝓛(η))` over nonempty Schubert unions** (Polo's Schubert filtrations,
  `Schubert.RS.Geometric.not_hasGeometricSchubertFiltration`).

The preimage ideals of unions are described by
`FlagVarieties.preimageIdeal_schubertUnion_eq_orbitIdeal_complex` and `Γ(X_w, 𝒪) = ℂ` is
`FlagVarieties.globalSectionsConstant_complex`: **the statements have no hypotheses**.
-/

open GLRep FlagVarieties FlagVarieties.SectionRep FlagVarieties.PointModel.Complex
    Demazure.SchubertUnions

namespace Schubert.RS.Geometric

noncomputable section

variable {n : ℕ}

/-- `L` is equivalent to a sheaf-theoretic section module `H⁰(X_S, 𝓛(η))` over a nonempty
Schubert union, `η` antidominant. -/
def IsGeometricSchubertLayer (V : Type*) [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borel ℂ n) V) : Prop :=
  ∃ k : SchubertLayerIndex n, Nonempty (L.Equiv (sectionsRep ℂ n (schubertUnion ℂ n k.1.2) k.1.1
    (isLeftTranslStable_of_eq (preimageIdeal_schubertUnion_eq_orbitIdeal_complex n _ k.2.2.1
        k.2.2.2))))

/-- The geometric and ring-model notions of Schubert layers agree. -/
theorem isGeometricSchubertLayer_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : Representation ℂ (borel ℂ n) V) :
    IsGeometricSchubertLayer V L ↔ IsSchubertLayer V L :=
  exists_congr fun k =>
    ⟨fun ⟨e⟩ =>
        ⟨e.trans (geometricSectionEquiv _ (preimageIdeal_schubertUnion_eq_orbitIdeal_complex n
        _ k.2.2.1 k.2.2.2) _ _)⟩,
      fun ⟨e⟩ =>
        ⟨e.trans
            (geometricSectionEquiv _ (preimageIdeal_schubertUnion_eq_orbitIdeal_complex n _ k.2.2.1
            k.2.2.2) _ _).symm⟩⟩

/-- The geometric dual Joseph modules are rational. -/
theorem isRationalBorelRep_dualJoseph (ν : Fin n → ℤ) :
    IsRationalBorelRep (FlagVarieties.dualJoseph ν) :=
  HasCoeffsIn.of_injective (SectionRep.isRationalBorelRep_dualJoseph ν)
    (dualJosephEquiv ν).toIntertwiningMap
    (dualJosephEquiv ν).toLinearEquiv.injective

open Family

variable (P : Parameters)

/-- **The sheaf-theoretic `P(−a) ⊗ P(−b)`** of the family. -/
abbrev geometricFamilyTensor :=
  (FlagVarieties.dualJoseph (negWeight (a P))).tprod (FlagVarieties.dualJoseph (negWeight (b P)))

variable {P}

theorem isRationalBorelRep_geometricFamilyTensor :
    IsRationalBorelRep (geometricFamilyTensor P) :=
  (isRationalBorelRep_dualJoseph _).tprod
    (isRationalBorelRep_dualJoseph _)

/-- **`ch(P(−a) ⊗ P(−b)) = κ_a κ_b`** for the sheaf-theoretic modules. -/
theorem ch_geometricFamilyTensor :
    ch (geometricFamilyTensor P) = toLaurent (key (a P) * key (b P)) := by
  rw [ch_tprod (isRationalBorelRep_dualJoseph _)
      (isRationalBorelRep_dualJoseph _),
    FlagVarieties.ch_dualJoseph_negWeight, FlagVarieties.ch_dualJoseph_negWeight, key_eq,
    key_eq, map_mul]
  rfl

/-- **Corollary 1.2 for the sheaf-theoretic modules (Polo's Schubert filtrations).** For
`(p − 2)(q − 2) > 2`, `P(−a) ⊗ P(−b)` admits no filtration whose layers are section modules
`H⁰(X_S, 𝓛(η))` over nonempty Schubert unions, for antidominant `η`. -/
theorem not_hasGeometricSchubertFiltration
    (hneg : 2 < ((P.p : ℤ) - 2) * ((P.q : ℤ) - 2)) :
    ¬ HasFiltrationBy IsGeometricSchubertLayer (geometricFamilyTensor P) := fun hF =>
  not_atomPositive P hneg <| atomPositive_of_hasFiltrationBy
    (fun _ _ _ _ hL => by
      obtain ⟨k, ⟨e⟩⟩ := (isGeometricSchubertLayer_iff _).mp hL
      exact (ch_eq_of_equiv e).symm ▸ isShiftedAtomSum_ch_sectionRep k.2.2.2 k.2.1)
    (isRationalBorelRep_geometricFamilyTensor) hF
    (ch_geometricFamilyTensor)

end

end Schubert.RS.Geometric
