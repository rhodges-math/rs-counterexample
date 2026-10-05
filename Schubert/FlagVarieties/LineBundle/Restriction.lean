import Schubert.FlagVarieties.LineBundle.Invertible

/-!
# The `B`-scheme `π⁻¹(X)` over a closed subscheme `X ⊆ Flₙ`

For a closed subscheme `X ⊆ Flₙ` (ideal sheaf `I`, closed immersion `i`), the preimage
`P_X = GLₙ ×_{Flₙ} X` carries the right action of `B` restricted from `GLₙ`:

* `FlagVarieties.preimageAction R n I : BorelAction R n X`, with `q = pr₂ : P_X ⟶ X`;
* `FlagVarieties.preimageHom R n I`: the inclusion `j : P_X ⟶ GLₙ` is equivariant over `i`;
* `FlagVarieties.preimageLocalData R n I v`: the local triviality data over `X ∩ bigCell v`,
  restricted from `GLₙ`;
* `FlagVarieties.lineBundleX R n I η`: the sheaf of semi-invariant functions on `P_X`, i.e.
  `𝓛(η)` built directly on `X`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

variable (R : Type u) [CommRing R] (n : ℕ) (I : (FlagScheme R n).IdealSheafData)

/-- `P_X = GLₙ ×_{Flₙ} X`. -/
abbrev preimageScheme : Scheme.{u} :=
  pullback (FlagScheme.orbitMap R n) I.subschemeι

/-- The closed immersion `j : P_X ⟶ GLₙ`. -/
abbrev preimageι : preimageScheme R n I ⟶ GLScheme R n :=
  pullback.fst (FlagScheme.orbitMap R n) I.subschemeι

/-- The projection `P_X ⟶ X`. -/
abbrev preimageProj : preimageScheme R n I ⟶ I.subscheme :=
  pullback.snd (FlagScheme.orbitMap R n) I.subschemeι

/-- The structure morphism `P_X ⟶ Spec R`. -/
abbrev preimageToSpec : preimageScheme R n I ⟶ Spec (CommRingCat.of R) :=
  preimageι R n I ≫ (GLOver R n).hom

/-- `P_X ×_R B`. -/
abbrev PreimageProd : Scheme.{u} :=
  pullback (preimageToSpec R n I) (BorelScheme.toSpec R n)

/-- `j × id : P_X ×_R B ⟶ GLₙ ×_R B`. -/
def preimageProdMap : PreimageProd R n I ⟶ GLBorel R n :=
  pullback.map _ _ _ _ (preimageι R n I) (𝟙 _) (𝟙 _) (by rw [Category.comp_id])
    (by rw [Category.comp_id, Category.id_comp])

theorem preimageAct_condition :
    (preimageProdMap R n I ≫ mulRight R n) ≫ FlagScheme.orbitMap R n =
      (pullback.fst _ _ ≫ preimageProj R n I) ≫ I.subschemeι := by
  rw [Category.assoc, mulRight_orbitMap, preimageProdMap, pullback.lift_fst_assoc,
    Category.assoc, pullback.condition, Category.assoc]

/-- The right action of `B` on `P_X`, `(g, x) · b = (g b, x)`. -/
def preimageAct : PreimageProd R n I ⟶ preimageScheme R n I :=
  pullback.lift (preimageProdMap R n I ≫ mulRight R n) (pullback.fst _ _ ≫ preimageProj R n I)
    (preimageAct_condition R n I)

/-- **`P_X ⟶ X` with the right action of `B`.** -/
def preimageAction : BorelAction R n I.subscheme where
  P := preimageScheme R n I
  q := preimageProj R n I
  toSpec := preimageToSpec R n I
  act := preimageAct R n I
  act_q := pullback.lift_snd _ _ _

/-- The inclusion `j : P_X ⟶ GLₙ` is equivariant over `i : X ⟶ Flₙ`. -/
def preimageHom : BorelAction.Hom (preimageAction R n I) (glBorelAction R n) I.subschemeι where
  j := preimageι R n I
  j_q := pullback.condition
  j_toSpec := rfl
  act_j := pullback.lift_fst _ _ _

/-- **`𝓛(η)` built on `X`**: the sheaf of `η`-semi-invariant functions on the fibres of
`P_X ⟶ X`. -/
abbrev lineBundleX (η : Fin n → ℤ) : I.subscheme.Modules :=
  (preimageAction R n I).semiInvariantSheaf η

/-- The comparison `i^* 𝓛(η) ⟶ 𝓛_X(η)`, restriction of semi-invariant functions to `P_X`. -/
abbrev lineBundleComparison (η : Fin n → ℤ) :
    (Scheme.Modules.pullback I.subschemeι).obj (lineBundle R n η) ⟶ lineBundleX R n I η :=
  (preimageHom R n I).pullbackSemiInvariantSheafMap η

/-! ### Local triviality over `X ∩ bigCell v` -/

variable (v : Equiv.Perm (Fin n))

/-- `X ∩ bigCell v`, as an open of `X`. -/
abbrev bigCellX : I.subscheme.Opens :=
  I.subschemeι ⁻¹ᵁ bigCell R v

/-- The section `s_v` over the big cell, as a morphism to `GLₙ`. -/
def bigCellE : (bigCell R v).toScheme ⟶ GLScheme R n :=
  (bigCellLocalData R v).e

/-- `g ↦ (s_v(π g), β(g))` on `π⁻¹(bigCell v)`, as a morphism to `GLₙ ×_R B`. -/
def bigCellT : (FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v).toScheme ⟶ GLBorel R n :=
  (bigCellLocalData R v).t

theorem bigCellE_orbitMap : bigCellE R n v ≫ FlagScheme.orbitMap R n = (bigCell R v).ι :=
  (bigCellLocalData R v).e_q

theorem bigCellT_mulRight :
    bigCellT R n v ≫ mulRight R n = (FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v).ι :=
  (bigCellLocalData R v).t_act

theorem bigCellT_fst : bigCellT R n v ≫ pullback.fst (GLOver R n).hom (BorelScheme.toSpec R n) =
    FlagScheme.orbitMap R n ∣_ bigCell R v ≫ bigCellE R n v :=
  (bigCellLocalData R v).t_actionFst

theorem preimageLocalData_e_condition :
    (I.subschemeι ∣_ bigCell R v ≫ bigCellE R n v) ≫ FlagScheme.orbitMap R n =
      (bigCellX R n I v).ι ≫ I.subschemeι := by
  rw [Category.assoc, bigCellE_orbitMap, morphismRestrict_ι]

/-- The section of `P_X ⟶ X` over `X ∩ bigCell v`, `x ↦ (s_v(x), x)`. -/
def preimageLocalDataE : (bigCellX R n I v).toScheme ⟶ preimageScheme R n I :=
  pullback.lift (I.subschemeι ∣_ bigCell R v ≫ bigCellE R n v) (bigCellX R n I v).ι
    (preimageLocalData_e_condition R n I v)

theorem range_preimage_le :
    Set.range ((preimageProj R n I ⁻¹ᵁ bigCellX R n I v).ι ≫ preimageι R n I) ⊆
      ((FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v : (GLScheme R n).Opens) : Set (GLScheme R n)) := by
  rintro _ ⟨x, rfl⟩
  have hx := x.2
  change I.subschemeι (preimageProj R n I x.1) ∈ bigCell R v at hx
  change FlagScheme.orbitMap R n (preimageι R n I x.1) ∈ bigCell R v
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact hx

/-- `p⁻¹(X ∩ bigCell v) ⟶ π⁻¹(bigCell v)`, the restriction of `j`. -/
def preimageRestrict : (preimageProj R n I ⁻¹ᵁ bigCellX R n I v).toScheme ⟶
    (FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v).toScheme :=
  IsOpenImmersion.lift (Scheme.Opens.ι _) _ (by
    rw [Scheme.Opens.range_ι]
    exact range_preimage_le R n I v)

@[reassoc] theorem preimageRestrict_ι :
    preimageRestrict R n I v ≫ (FlagScheme.orbitMap R n ⁻¹ᵁ bigCell R v).ι =
      (preimageProj R n I ⁻¹ᵁ bigCellX R n I v).ι ≫ preimageι R n I :=
  IsOpenImmersion.lift_fac _ _ _

theorem preimageRestrict_key :
    preimageProj R n I ∣_ bigCellX R n I v ≫ I.subschemeι ∣_ bigCell R v =
      preimageRestrict R n I v ≫ FlagScheme.orbitMap R n ∣_ bigCell R v := by
  rw [← cancel_mono (bigCell R v).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    morphismRestrict_ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    preimageRestrict_ι_assoc, pullback.condition]

/-- `x ↦ β(j x)`, the `B`-component of the trivialization restricted to `P_X`. -/
def preimageLocalDataβ : (preimageProj R n I ⁻¹ᵁ bigCellX R n I v).toScheme ⟶ BorelScheme R n :=
  preimageRestrict R n I v ≫ bigCellT R n v ≫ pullback.snd _ _

theorem preimageLocalData_t_condition :
    (preimageProj R n I ∣_ bigCellX R n I v ≫ preimageLocalDataE R n I v) ≫
        preimageToSpec R n I =
      preimageLocalDataβ R n I v ≫ BorelScheme.toSpec R n := by
  have h1 : preimageLocalDataE R n I v ≫ preimageι R n I =
      I.subschemeι ∣_ bigCell R v ≫ bigCellE R n v :=
    pullback.lift_fst _ _ _
  have h2 : bigCellT R n v ≫ pullback.snd _ _ ≫ BorelScheme.toSpec R n =
      bigCellT R n v ≫ pullback.fst _ _ ≫ (GLOver R n).hom := by
    rw [pullback.condition]
  change _ = preimageRestrict R n I v ≫ bigCellT R n v ≫ pullback.snd _ _ ≫
    BorelScheme.toSpec R n
  rw [h2, ← Category.assoc (bigCellT R n v), bigCellT_fst]
  simp only [preimageToSpec, Category.assoc]
  rw [reassoc_of% h1, ← Category.assoc, ← Category.assoc, preimageRestrict_key]
  simp only [Category.assoc]

/-- `x ↦ ((s_v(p x), p x), β(j x))`. -/
def preimageLocalDataT : (preimageProj R n I ⁻¹ᵁ bigCellX R n I v).toScheme ⟶ PreimageProd R n I :=
  pullback.lift (preimageProj R n I ∣_ bigCellX R n I v ≫ preimageLocalDataE R n I v)
    (preimageLocalDataβ R n I v) (preimageLocalData_t_condition R n I v)

theorem preimageLocalDataT_prodMap :
    preimageLocalDataT R n I v ≫ preimageProdMap R n I =
      preimageRestrict R n I v ≫ bigCellT R n v := by
  apply pullback.hom_ext
  · rw [Category.assoc, preimageProdMap, pullback.lift_fst, ← Category.assoc,
      preimageLocalDataT, pullback.lift_fst, Category.assoc, preimageLocalDataE,
      pullback.lift_fst, Category.assoc]
    rw [bigCellT_fst, ← Category.assoc, ← Category.assoc,
      preimageRestrict_key]
  · rw [Category.assoc, preimageProdMap, pullback.lift_snd, Category.comp_id,
      preimageLocalDataT, pullback.lift_snd, preimageLocalDataβ, Category.assoc]

/-- **Local triviality data of `P_X ⟶ X` over `X ∩ bigCell v`**, restricted from `GLₙ`. -/
def preimageLocalData : (preimageAction R n I).LocalData (bigCellX R n I v) where
  e := preimageLocalDataE R n I v
  e_q := pullback.lift_snd _ _ _
  t := preimageLocalDataT R n I v
  t_act := by
    change preimageLocalDataT R n I v ≫ preimageAct R n I = _
    apply pullback.hom_ext
    · rw [Category.assoc, preimageAct, pullback.lift_fst, ← Category.assoc,
        preimageLocalDataT_prodMap, Category.assoc]
      rw [bigCellT_mulRight]
      exact preimageRestrict_ι R n I v
    · rw [Category.assoc, preimageAct, pullback.lift_snd, ← Category.assoc,
        preimageLocalDataT, pullback.lift_fst, Category.assoc, preimageLocalDataE,
        pullback.lift_snd]
      exact morphismRestrict_ι _ _
  t_actionFst := pullback.lift_fst _ _ _

end FlagVarieties
