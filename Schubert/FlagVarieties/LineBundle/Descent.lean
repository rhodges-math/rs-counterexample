import Schubert.FlagVarieties.LineBundle.Equivariant

/-!
# Semi-invariant functions on a locally trivial `B`-scheme

Let `q : P ⟶ T` carry a right `B`-action (`FlagVarieties.BorelAction`), and suppose that over an
open `V ⊆ T` it is trivial in the following sense (`BorelAction.LocalData`): there is a section
`e : V ⟶ P` of `q`, and a morphism `t : q⁻¹(V) ⟶ P ×_R B`, `x ↦ (e(q x), β(x))`, with
`x = e(q x) · β(x)`. Put `σ = β^* η⁻¹`, a unit on `q⁻¹(V)`.

* `BorelAction.LocalData.eq_mul_trivializingSection`: every semi-invariant function `f` on `q⁻¹(W)`,
  `W ⊆ V`, is `f = q^* a · σ` with `a = e^* f`;
* `BorelAction.LocalData.eq_of_mul_trivializingSection_eq`: the coefficient `a` is unique;
* `BorelAction.IsSemiInvariant.q_mul`: conversely, if `σ` is semi-invariant then so is
  every `q^* a · σ`.
-/

noncomputable section

namespace FlagVarieties

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

theorem le_preimage_top {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) : U ≤ f ⁻¹ᵁ ⊤ := by
  simp

/-- A restriction map of a scheme along an equality of opens is an isomorphism. -/
theorem isIso_presheaf_map_of_eq {X : Scheme.{u}} {U U' : X.Opens} (i : U ⟶ U') (h : U = U') :
    IsIso (X.presheaf.map i.op) := by
  subst h
  rw [Subsingleton.elim i (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  infer_instance

/-- For `W ≤ V`, restricting functions on `W` to the open subscheme `V` is bijective. -/
theorem isIso_ι_app {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V) : IsIso (V.ι.app W) := by
  rw [Scheme.Opens.ι_app]
  apply isIso_presheaf_map_of_eq
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

theorem ι_app_injective {X : Scheme.{u}} {V W : X.Opens} (h : W ≤ V) :
    Function.Injective (V.ι.app W).hom := by
  have := isIso_ι_app h
  exact (ConcreteCategory.bijective_of_isIso (V.ι.app W)).1

namespace BorelAction

variable {R : Type u} [CommRing R] {n : ℕ} {T : Scheme.{u}} (E : BorelAction R n T)

/-- Local triviality data of `E` over an open `V ⊆ T`: a section `e` of `q` over `V`, and
`t : q⁻¹(V) ⟶ P ×_R B`, `x ↦ (e(q x), β(x))`, with `x = e(q x) · β(x)`. -/
structure LocalData (V : T.Opens) where
  /-- A section of `q` over `V`. -/
  e : V.toScheme ⟶ E.P
  e_q : e ≫ E.q = V.ι
  /-- `x ↦ (e(q x), β(x))`. -/
  t : (E.q ⁻¹ᵁ V).toScheme ⟶ E.actionDomain
  t_act : t ≫ E.act = (E.q ⁻¹ᵁ V).ι
  t_actionFst : t ≫ E.actionFst = E.q ∣_ V ≫ e

/-- The open `q⁻¹(W)` of the open subscheme `q⁻¹(V)`. -/
abbrev preimageOpen (V W : T.Opens) : (E.q ⁻¹ᵁ V).toScheme.Opens :=
  (E.q ⁻¹ᵁ V).ι ⁻¹ᵁ E.q ⁻¹ᵁ W

theorem preimageOpen_eq (V W : T.Opens) : E.preimageOpen V W = (E.q ∣_ V) ⁻¹ᵁ V.ι ⁻¹ᵁ W := by
  change ((E.q ⁻¹ᵁ V).ι ≫ E.q) ⁻¹ᵁ W = (E.q ∣_ V ≫ V.ι) ⁻¹ᵁ W
  rw [morphismRestrict_ι]

/-- Restriction of functions to the open subscheme `q⁻¹(V)`. -/
abbrev restrictPreimage (V W : T.Opens) : Γ(E.P, E.q ⁻¹ᵁ W) ⟶
    Γ((E.q ⁻¹ᵁ V).toScheme, E.preimageOpen V W) :=
  (E.q ⁻¹ᵁ V).ι.app (E.q ⁻¹ᵁ W)

theorem restrictPreimage_q (V W : T.Opens) (a : Γ(T, W)) :
    (E.restrictPreimage V W).hom ((E.q.app W).hom a) =
      ((E.q ∣_ V).appLE (V.ι ⁻¹ᵁ W) (E.preimageOpen V W) (E.preimageOpen_eq V W).le).hom
          ((V.ι.app W).hom a) := by
  rw [show E.restrictPreimage V W = (E.q ⁻¹ᵁ V).ι.app (E.q ⁻¹ᵁ W) from rfl, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  have h1 : E.preimageOpen V W ≤ ((E.q ⁻¹ᵁ V).ι ≫ E.q) ⁻¹ᵁ W := le_rfl
  have h2 : E.preimageOpen V W ≤ (E.q ∣_ V ≫ V.ι) ⁻¹ᵁ W := (E.preimageOpen_eq V W).le
  exact (appLE_comp_apply (E.q ⁻¹ᵁ V).ι E.q le_rfl le_rfl h1 a).symm.trans
    ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (appLE_eq_of_eq (morphismRestrict_ι E.q V).symm h1 h2)) a).trans
      (appLE_comp_apply (E.q ∣_ V) V.ι le_rfl (E.preimageOpen_eq V W).le h2 a))


theorem isIso_restrictPreimage {V W : T.Opens} (hW : W ≤ V) : IsIso (E.restrictPreimage V W) :=
  isIso_ι_app (E.q.preimage_mono hW)

theorem restrictPreimage_injective {V W : T.Opens} (hW : W ≤ V) :
    Function.Injective (E.restrictPreimage V W).hom :=
  ι_app_injective (E.q.preimage_mono hW)

theorem restrictPreimage_map {V W : T.Opens} (hW : W ≤ V) (f : Γ(E.P, E.q ⁻¹ᵁ V)) :
    (E.restrictPreimage V W).hom ((E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom f) =
      ((E.q ⁻¹ᵁ V).toScheme.presheaf.map
        (homOfLE ((E.q ⁻¹ᵁ V).ι.preimage_mono (E.q.preimage_mono hW))).op).hom
        ((E.restrictPreimage V V).hom f) := by
  change (E.P.presheaf.map _ ≫ (E.q ⁻¹ᵁ V).ι.app _).hom f =
    ((E.q ⁻¹ᵁ V).ι.app _ ≫ (E.q ⁻¹ᵁ V).toScheme.presheaf.map _).hom f
  rw [Scheme.Hom.naturality]
  rfl


/-- Functions pulled back from the base are invariant: `a^* q^* a = pr₁^* q^* a`. -/
theorem act_q_app (W : T.Opens) (a : Γ(T, W)) :
    (E.act.appLE _ _ (E.actionFst_preimage_le W)).hom ((E.q.app W).hom a) =
      (E.actionFst.app (E.q ⁻¹ᵁ W)).hom ((E.q.app W).hom a) := by
  have h₁ : E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W ≤ (E.act ≫ E.q) ⁻¹ᵁ W := E.actionFst_preimage_le W
  have h₂ : E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ W ≤ (E.actionFst ≫ E.q) ⁻¹ᵁ W := le_rfl
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  exact (appLE_comp_apply E.act E.q le_rfl _ h₁ a).symm.trans
    ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (appLE_eq_of_eq E.act_q h₁ h₂)) a).trans
      (appLE_comp_apply E.actionFst E.q le_rfl le_rfl h₂ a))

theorem isUnit_twist (η : Fin n → ℤ) : IsUnit (E.twist η) :=
  (((Units.isUnit _).map _).map _ : IsUnit _)

theorem isUnit_twistOn (η : Fin n → ℤ) (W : E.actionDomain.Opens) : IsUnit (E.twistOn η W) :=
  (E.isUnit_twist η).map _

/-- A product of a function pulled back from the base and a semi-invariant function is
semi-invariant. -/
theorem IsSemiInvariant.q_mul {η : Fin n → ℤ} {W : T.Opens} (a : Γ(T, W))
    {f : Γ(E.P, E.q ⁻¹ᵁ W)} (hf : E.IsSemiInvariant η f) :
    E.IsSemiInvariant η ((E.q.app W).hom a * f) := by
  unfold IsSemiInvariant at hf ⊢
  rw [map_mul, map_mul, hf, E.act_q_app]
  ring

theorem semiInvariantι_app_smul_map (η : Fin n → ℤ) {V W : T.Opens} (hW : W ≤ V) (a : Γ(T, W))
    (s : Γ(E.semiInvariantSheaf η, V)) :
    ((E.semiInvariantι η).app W).hom
        (a • ((E.semiInvariantSheaf η).presheaf.map (homOfLE hW).op).hom s) =
      (E.q.app W).hom a * (E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom
        (((E.semiInvariantι η).app V).hom s) := by
  rw [Scheme.Modules.Hom.app_smul]
  have h := ConcreteCategory.congr_hom
    ((E.semiInvariantι η).mapPresheaf.naturality (homOfLE hW).op) s
  change ((E.semiInvariantι η).app W).hom (((E.semiInvariantSheaf η).presheaf.map _).hom s) =
    (E.directImage.presheaf.map _).hom (((E.semiInvariantι η).app V).hom s) at h
  rw [h]
  rfl

namespace LocalData

variable {E} {V : T.Opens} (D : E.LocalData V)


theorem e_preimage_le {W : T.Opens} : V.ι ⁻¹ᵁ W ≤ D.e ⁻¹ᵁ E.q ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, D.e_q]

/-- `f ↦ e^* f`. -/
def evalAlongSection (W : T.Opens) : Γ(E.P, E.q ⁻¹ᵁ W) ⟶ Γ(V.toScheme, V.ι ⁻¹ᵁ W) :=
  D.e.appLE (E.q ⁻¹ᵁ W) (V.ι ⁻¹ᵁ W) D.e_preimage_le

theorem evalAlongSection_q (W : T.Opens) (a : Γ(T, W)) :
    (D.evalAlongSection W).hom ((E.q.app W).hom a) = (V.ι.app W).hom a := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  have h : V.ι ⁻¹ᵁ W ≤ (D.e ≫ E.q) ⁻¹ᵁ W := by rw [D.e_q]
  exact (appLE_comp_apply D.e E.q le_rfl D.e_preimage_le h a).symm.trans
    (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (appLE_eq_of_eq D.e_q h le_rfl)) a)

theorem preimageOpen_le_t (W : T.Opens) : E.preimageOpen V W ≤ D.t ⁻¹ᵁ E.actionFst ⁻¹ᵁ E.q ⁻¹ᵁ
    W := by
  have h : D.t ≫ E.actionFst ≫ E.q = E.q ∣_ V ≫ V.ι := by
    rw [← Category.assoc, D.t_actionFst, Category.assoc, D.e_q]
  rw [E.preimageOpen_eq]
  exact (congrArg (fun f => f ⁻¹ᵁ W) h).ge

/-- The function `σ = β^* η⁻¹` on `q⁻¹(V)`. -/
def trivializingSection (η : Fin n → ℤ) : Γ(E.P, E.q ⁻¹ᵁ V) :=
  have := E.isIso_restrictPreimage (le_refl V)
  (inv (E.restrictPreimage V V)).hom ((D.t.appLE ⊤ (E.preimageOpen V V) (le_preimage_top D.t _)).hom
      (E.twist η))

theorem restrictPreimage_trivializingSection (η : Fin n → ℤ) {W : T.Opens} (hW : W ≤ V) :
    (E.restrictPreimage V W).hom ((E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom
        (D.trivializingSection η)) =
      (D.t.appLE _ (E.preimageOpen V W) (D.preimageOpen_le_t W)).hom (E.twistOn η _) := by
  have := E.isIso_restrictPreimage (le_refl V)
  have e1 : ∀ y, (E.restrictPreimage V V).hom ((inv (E.restrictPreimage V V)).hom y) = y :=
      fun y => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, IsIso.inv_hom_id, CommRingCat.hom_id,
      RingHom.id_apply]
  rw [E.restrictPreimage_map hW, trivializingSection, e1]
  have e2 : ((E.q ⁻¹ᵁ V).toScheme.presheaf.map
      (homOfLE ((E.q ⁻¹ᵁ V).ι.preimage_mono (E.q.preimage_mono hW))).op).hom
        ((D.t.appLE ⊤ (E.preimageOpen V V) (le_preimage_top D.t _)).hom (E.twist η)) =
      (D.t.appLE ⊤ (E.preimageOpen V W) (le_preimage_top D.t _)).hom (E.twist η) := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  have e3 : (D.t.appLE _ (E.preimageOpen V W) (D.preimageOpen_le_t W)).hom (E.twistOn η _) =
      (D.t.appLE ⊤ (E.preimageOpen V W) (le_preimage_top D.t _)).hom (E.twist η) := by
    rw [twistOn, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  rw [e2, e3]

theorem restrictPreimage_eq (W : T.Opens) (f : Γ(E.P, E.q ⁻¹ᵁ W)) :
    (E.restrictPreimage V W).hom f = (D.t.appLE _ (E.preimageOpen V W) (D.preimageOpen_le_t W)).hom
      ((E.act.appLE _ _ (E.actionFst_preimage_le W)).hom f) := by
  have h : E.preimageOpen V W ≤ (D.t ≫ E.act) ⁻¹ᵁ E.q ⁻¹ᵁ W :=
    (congrArg (fun g => g ⁻¹ᵁ E.q ⁻¹ᵁ W) D.t_act).ge
  rw [show E.restrictPreimage V W = (E.q ⁻¹ᵁ V).ι.app (E.q ⁻¹ᵁ W) from rfl, Scheme.Hom.app_eq_appLE]
  exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (appLE_eq_of_eq D.t_act.symm le_rfl h)) f).trans
    (appLE_comp_apply D.t E.act (E.actionFst_preimage_le W) (D.preimageOpen_le_t W) h f)

theorem t_actionFst_apply (W : T.Opens) (f : Γ(E.P, E.q ⁻¹ᵁ W)) :
    (D.t.appLE _ (E.preimageOpen V W) (D.preimageOpen_le_t W)).hom
        ((E.actionFst.app (E.q ⁻¹ᵁ W)).hom f) =
      ((E.q ∣_ V).appLE (V.ι ⁻¹ᵁ W) (E.preimageOpen V W) (E.preimageOpen_eq V W).le).hom
          ((D.evalAlongSection W).hom f) := by
  have h₁ : E.preimageOpen V W ≤ (D.t ≫ E.actionFst) ⁻¹ᵁ E.q ⁻¹ᵁ W := D.preimageOpen_le_t W
  have h₂ : E.preimageOpen V W ≤ (E.q ∣_ V ≫ D.e) ⁻¹ᵁ E.q ⁻¹ᵁ W :=
    (E.preimageOpen_eq V W).le.trans ((E.q ∣_ V).preimage_mono D.e_preimage_le)
  rw [Scheme.Hom.app_eq_appLE]
  exact (appLE_comp_apply D.t E.actionFst le_rfl (D.preimageOpen_le_t W) h₁ f).symm.trans
    ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (appLE_eq_of_eq D.t_actionFst h₁ h₂))
        f).trans
      (appLE_comp_apply (E.q ∣_ V) D.e D.e_preimage_le (E.preimageOpen_eq V W).le h₂ f))

/-- The coefficient `a = e^* f ∈ Γ(T, W)` of a function `f` on `q⁻¹(W)`. -/
def coeff {W : T.Opens} (hW : W ≤ V) (f : Γ(E.P, E.q ⁻¹ᵁ W)) : Γ(T, W) :=
  have := isIso_ι_app hW
  (inv (V.ι.app W)).hom ((D.evalAlongSection W).hom f)

theorem ι_app_coeff {W : T.Opens} (hW : W ≤ V) (f : Γ(E.P, E.q ⁻¹ᵁ W)) :
    (V.ι.app W).hom (D.coeff hW f) = (D.evalAlongSection W).hom f := by
  have := isIso_ι_app hW
  rw [coeff, ← RingHom.comp_apply, ← CommRingCat.hom_comp, IsIso.inv_hom_id, CommRingCat.hom_id,
    RingHom.id_apply]

theorem coeff_q {W : T.Opens} (hW : W ≤ V) (a : Γ(T, W)) :
    D.coeff hW ((E.q.app W).hom a) = a := by
  apply ι_app_injective hW
  rw [ι_app_coeff, evalAlongSection_q]

/-- **Descent**: every semi-invariant function on `q⁻¹(W)`, `W ⊆ V`, is `q^* a · σ`, with
`a = e^* f`. -/
theorem eq_mul_trivializingSection (η : Fin n → ℤ) {W : T.Opens} (hW : W ≤ V)
    {f : Γ(E.P, E.q ⁻¹ᵁ W)}
    (hf : E.IsSemiInvariant η f) :
    f = (E.q.app W).hom (D.coeff hW f) *
      (E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom (D.trivializingSection η) := by
  apply E.restrictPreimage_injective hW
  rw [map_mul, E.restrictPreimage_q, D.ι_app_coeff, D.restrictPreimage_trivializingSection η hW,
      D.restrictPreimage_eq, hf, map_mul, D.t_actionFst_apply, mul_comm]

theorem isUnit_trivializingSection (η : Fin n → ℤ) : IsUnit (D.trivializingSection η) := by
  have := E.isIso_restrictPreimage (le_refl V)
  exact ((E.isUnit_twist η).map _).map _

/-- The coefficient in the descent is unique. -/
theorem eq_of_mul_trivializingSection_eq (η : Fin n → ℤ) {W : T.Opens} (hW : W ≤ V) {a b : Γ(T, W)}
    (h : (E.q.app W).hom a *
        (E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom (D.trivializingSection η) =
      (E.q.app W).hom b *
        (E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom (D.trivializingSection η)) :
            a = b := by
  have hu := (D.isUnit_trivializingSection η).map
      (E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom
  rw [← D.coeff_q hW a, ← D.coeff_q hW b, hu.mul_left_inj.mp h]

/-- **Local freeness of the semi-invariant sheaf.** If `s₀` is a section over `V` given by `σ`
(so `σ` is semi-invariant), then on every open `W ⊆ V` the sections are `Γ(T, W) · s₀|_W`,
freely. -/
theorem bijective_smul_section (η : Fin n → ℤ) {W : T.Opens} (hW : W ≤ V)
    (s₀ : Γ(E.semiInvariantSheaf η, V))
    (hs₀ : ((E.semiInvariantι η).app V).hom s₀ = D.trivializingSection η) :
    Function.Bijective
      (fun a : Γ(T, W) => a • ((E.semiInvariantSheaf η).presheaf.map (homOfLE hW).op).hom s₀) := by
  have hι := kernel_ι_app_injective (E.pullbackAct - E.pullbackTwist η) W
  constructor
  · intro a b hab
    have h := congrArg ((E.semiInvariantι η).app W).hom hab
    rw [E.semiInvariantι_app_smul_map η hW, E.semiInvariantι_app_smul_map η hW, hs₀] at h
    exact D.eq_of_mul_trivializingSection_eq η hW h
  · intro s
    have hs : E.IsSemiInvariant η (W := W) (((E.semiInvariantι η).app W).hom s) :=
      (E.mem_range_semiInvariantι_app_iff η W _).mp ⟨s, rfl⟩
    refine ⟨D.coeff hW (((E.semiInvariantι η).app W).hom s), hι ?_⟩
    change ((E.semiInvariantι η).app W).hom _ = ((E.semiInvariantι η).app W).hom s
    rw [E.semiInvariantι_app_smul_map η hW, hs₀]
    exact (D.eq_mul_trivializingSection η hW hs).symm

include D in
theorem coeff_isUnit {W : T.Opens} (hW : W ≤ V) {c : Γ(T, W)} (hc : IsUnit ((E.q.app W).hom c)) :
    IsUnit c := by
  rw [← D.coeff_q hW c]
  have := isIso_ι_app hW
  exact (hc.map (D.evalAlongSection W).hom).map (inv (V.ι.app W)).hom

include D in
/-- **Local freeness of the semi-invariant sheaf**, with any basis: if `s₀` is a section over `V`
whose function is a unit, then on every open `W ⊆ V` the sections are `Γ(T, W) · s₀|_W`,
freely. -/
theorem bijective_smul_section_of_isUnit (η : Fin n → ℤ) {W : T.Opens} (hW : W ≤ V)
    (s₀ : Γ(E.semiInvariantSheaf η, V))
    (hu : IsUnit (show Γ(E.P, E.q ⁻¹ᵁ V) from ((E.semiInvariantι η).app V).hom s₀)) :
    Function.Bijective
      (fun a : Γ(T, W) => a • ((E.semiInvariantSheaf η).presheaf.map (homOfLE hW).op).hom s₀) := by
  have hι := kernel_ι_app_injective (E.pullbackAct - E.pullbackTwist η) W
  set τ : Γ(E.P, E.q ⁻¹ᵁ V) := ((E.semiInvariantι η).app V).hom s₀ with hτ
  set τW : Γ(E.P, E.q ⁻¹ᵁ W) := (E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom τ
  have huW : IsUnit τW := hu.map _
  have hτs : E.IsSemiInvariant η τ := (E.mem_range_semiInvariantι_app_iff η V _).mp ⟨s₀, rfl⟩
  have hτW : E.IsSemiInvariant η τW := BorelAction.IsSemiInvariant.map E hW hτs
  constructor
  · intro a b hab
    have h := congrArg ((E.semiInvariantι η).app W).hom hab
    rw [E.semiInvariantι_app_smul_map η hW, E.semiInvariantι_app_smul_map η hW] at h
    rw [← D.coeff_q hW a, ← D.coeff_q hW b, huW.mul_left_inj.mp h]
  · intro s
    set f : Γ(E.P, E.q ⁻¹ᵁ W) := ((E.semiInvariantι η).app W).hom s with hfdef
    have hs : E.IsSemiInvariant η f := (E.mem_range_semiInvariantι_app_iff η W _).mp ⟨s, rfl⟩
    have e1 := D.eq_mul_trivializingSection η hW hs
    have e2 := D.eq_mul_trivializingSection η hW hτW
    set σW : Γ(E.P, E.q ⁻¹ᵁ W) := (E.P.presheaf.map (homOfLE (E.q.preimage_mono hW)).op).hom
      (D.trivializingSection η)
    have hc : IsUnit (D.coeff hW τW) := by
      apply D.coeff_isUnit hW
      have h3 : IsUnit ((E.q.app W).hom (D.coeff hW τW) * σW) := e2 ▸ huW
      exact isUnit_of_mul_isUnit_left h3
    refine ⟨D.coeff hW f * ↑hc.unit⁻¹, hι ?_⟩
    refine (E.semiInvariantι_app_smul_map η hW _ s₀).trans ?_
    have key : (E.q.app W).hom (D.coeff hW f * ↑hc.unit⁻¹) * τW =
        (E.q.app W).hom (D.coeff hW f) * σW := by
      refine (congrArg (fun x => (E.q.app W).hom (D.coeff hW f * ↑hc.unit⁻¹) * x) e2).trans ?_
      rw [map_mul, mul_assoc, ← mul_assoc ((E.q.app W).hom ↑hc.unit⁻¹), ← map_mul,
        IsUnit.val_inv_mul, map_one, one_mul]
    exact key.trans e1.symm

end LocalData

end BorelAction

end FlagVarieties
