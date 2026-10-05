import Schubert.Demazure.SchubertUnions.OrbitDuality
import Schubert.Demazure.SchubertUnions.RightKey
import Schubert.Demazure.SchubertUnions.Coset
import Schubert.Demazure.JosephPolo.TableauKeys
import Schubert.Demazure.Filtrations.SectionModules

/-!
# Characters of sums of Demazure modules over Bruhat ideals

Fix an ordered column sequence `h` with shape `m = columnMultiplicity h`. For a lower set `I`
of permutations in Bruhat order (a union of Schubert varieties `X_I`), the weight
multiplicities of `D_I = Σ_{w ∈ I} D_w` are counted by the tuples of row sets with a defining
chain bounded by some element of `I` (`finrank_demazureUnion_inf_eq`):

  `dim (D_I)_μ = #{T ∈ chainSet h I | wt T = μ}`.

The proof is by induction on `I`, removing a maximal element `σ`:

* upper bound: `D_I = D_{I∖σ} + D_σ`, whose intersection contains `D_{[e,σ)}`; the right-key
  lemma identifies the overlap of the corresponding tuple sets with `chainSet h [e,σ)`;
* lower bound: standard-monomial independence on unions of orbits
  (`card_chainSet_le_finrank`).

As a consequence, intersections of such sums are sums over intersections of the ideals
(`demazureUnion_inf`), the algebraic counterpart of the reducedness of intersections of unions
of Schubert varieties.
-/

open Schubert

namespace Demazure.SchubertUnions

open FlagModule Filtrations BModules FinPermutation

noncomputable section

variable {n d : ℕ}

/-! ### Weights of tuples -/

/-- The weight `(#{j | i ∈ T j})_i` of a tuple of row sets. -/
def tupleWeight (h : Fin d → Fin n) (T : (j : Fin d) → FlagMinorRowSet (h j)) : Weight n :=
  fun i => (flagTupleWeight h T i : ℤ)

/-- The number of tuples of weight `μ` with a defining chain bounded by an element of `S`. -/
def chainCount (h : Fin d → Fin n) (S : Finset (FinPermutation n)) (μ : Weight n) : ℕ :=
  ((chainSet h S).filter fun T => tupleWeight h T = μ).card

/-- The polynomial `Σ_{T ∈ chainSet h S} x^{wt T}`. -/
def chainCharacter (h : Fin d → Fin n) (S : Finset (FinPermutation n)) : Polynomial n :=
  ∑ T ∈ chainSet h S, compositionMonomial (flagTupleWeight h T)

theorem toLaurent_compositionMonomial (a : Composition n) :
    toLaurent (compositionMonomial a) =
      (AddMonoidAlgebra.single (fun i => (a i : ℤ)) (1 : ℤ) : Laurent n) := by
  rw [compositionMonomial, toLaurent_monomial]
  rfl

theorem coeff_compositionMonomial_tuple (h : Fin d → Fin n)
    (T : (j : Fin d) → FlagMinorRowSet (h j)) (μ : Weight n) :
    (toLaurent (compositionMonomial (flagTupleWeight h T))).coeff μ =
      if tupleWeight h T = μ then 1 else 0 := by
  rw [toLaurent_compositionMonomial, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rfl

theorem coeff_chainCharacter (h : Fin d → Fin n) (S : Finset (FinPermutation n)) (μ : Weight n) :
    (toLaurent (chainCharacter h S)).coeff μ = chainCount h S μ := by
  rw [chainCharacter, map_sum, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp only [coeff_compositionMonomial_tuple]
  rw [Finset.sum_boole]
  rfl

/-! ### Weight spaces of torus-stable spaces of matrix polynomials -/

/-- The weight space `E_μ` of matrix polynomials. -/
abbrev ambientWeight (μ : Weight n) : Submodule ℂ (MatrixPolynomial n) :=
  torusWeightSpace (polynomialTorus n) μ

theorem le_iSup_inf_ambientWeight (A : Submodule ℂ (MatrixPolynomial n))
    (hA : ∀ t, ∀ p ∈ A, polynomialTorus n t p ∈ A) :
    A ≤ ⨆ ν : Weight n, A ⊓ ambientWeight ν := by
  calc A = polynomialWeightSpan A := (polynomialWeightSpan_eq A fun t p hp => hA t p hp).symm
    _ ≤ _ := by
      refine Submodule.span_le.mpr ?_
      rintro p ⟨hpA, v, hv⟩
      exact (le_iSup (fun ν => A ⊓ ambientWeight ν) v) ⟨hpA, hv⟩

/-- Weight spaces of a sum of torus-stable subspaces. -/
theorem sup_inf_ambientWeight (A B : Submodule ℂ (MatrixPolynomial n))
    (hA : ∀ t, ∀ p ∈ A, polynomialTorus n t p ∈ A) (hB : ∀ t, ∀ p ∈ B, polynomialTorus n t p ∈ B)
    (μ : Weight n) :
    (A ⊔ B) ⊓ ambientWeight μ = (A ⊓ ambientWeight μ) ⊔ (B ⊓ ambientWeight μ) := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right))
  rintro x ⟨hx, hxμ⟩
  have hsplit : ∀ C : Submodule ℂ (MatrixPolynomial n),
      (∀ t, ∀ p ∈ C, polynomialTorus n t p ∈ C) → ∀ c ∈ C, ∃ c₁ ∈ C ⊓ ambientWeight μ,
        c - c₁ ∈ ⨆ (ν : Weight n) (_ : ν ≠ μ), ambientWeight ν := by
    intro C hC c hc
    have h1 := le_iSup_inf_ambientWeight C hC hc
    rw [iSup_split_single _ μ] at h1
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := Submodule.mem_sup.mp h1
    refine ⟨c₁, hc₁, ?_⟩
    rw [add_sub_cancel_left]
    have hmono : (⨆ (ν : Weight n) (_ : ν ≠ μ), C ⊓ ambientWeight ν) ≤
        ⨆ (ν : Weight n) (_ : ν ≠ μ), ambientWeight ν := iSup₂_mono fun ν _ => inf_le_right
    exact hmono hc₂
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a₁, ha₁, ha₂⟩ := hsplit A hA a ha
  obtain ⟨b₁, hb₁, hb₂⟩ := hsplit B hB b hb
  have hy : (a + b) - (a₁ + b₁) ∈ ambientWeight μ :=
    Submodule.sub_mem _ hxμ (Submodule.add_mem _ ha₁.2 hb₁.2)
  have hy' : (a + b) - (a₁ + b₁) ∈ ⨆ (ν : Weight n) (_ : ν ≠ μ), ambientWeight ν := by
    have := Submodule.add_mem _ ha₂ hb₂
    rwa [show a - a₁ + (b - b₁) = (a + b) - (a₁ + b₁) by abel] at this
  have h0 := (Submodule.disjoint_def.mp (torusWeightSpace_iSupIndep (polynomialTorus n) μ)) _
    hy hy'
  rw [sub_eq_zero] at h0
  rw [h0]
  exact Submodule.add_mem_sup ha₁ hb₁

/-- The dimension of a finite sum of subspaces of a finite-dimensional space. -/
theorem finrank_biSup_le {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [DecidableEq ι]
    (D : Submodule ℂ V) [FiniteDimensional ℂ D] (p : ι → Submodule ℂ V) (hp : ∀ i, p i ≤ D)
    (F : Finset ι) :
    Module.finrank ℂ (⨆ i ∈ F, p i : Submodule ℂ V) ≤ ∑ i ∈ F, Module.finrank ℂ (p i) := by
  induction F using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), p i) = ⊥ by simp]
    simp
  | insert a F ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    have : FiniteDimensional ℂ (p a) := Submodule.finiteDimensional_of_le (hp a)
    have : FiniteDimensional ℂ (⨆ i ∈ F, p i : Submodule ℂ V) :=
      Submodule.finiteDimensional_of_le (iSup₂_le fun i _ => hp i)
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

/-! ### Single Demazure modules -/

open Classical in
theorem chainSet_singleton_filter (h : Fin d → Fin n) (σ : FinPermutation n) (μ : Weight n) :
    chainCount h {σ} μ =
      (Finset.univ.filter fun T => HasFlagDefiningChain h T σ ∧ tupleWeight h T = μ).card := by
  classical
  unfold chainCount
  congr 1
  ext T
  simp [mem_chainSet]

theorem finrank_flagDemazure_inf (h : Fin d → Fin n) (σ : FinPermutation n) (μ : Weight n) :
    Module.finrank ℂ (flagDemazure (columnMultiplicity h) σ ⊓ ambientWeight μ :
      Submodule ℂ (MatrixPolynomial n)) = chainCount h {σ} μ := by
  classical
  have hw : torusWeightSpace (flagTorus (columnMultiplicity h) σ) μ =
      (ambientWeight μ).comap (flagDemazure (columnMultiplicity h) σ).subtype := by
    ext x
    exact ⟨fun hx t => congrArg Subtype.val (hx t), fun hx t => Subtype.ext (hx t)⟩
  have hc := flagDemazure_hasTorusCharacter (columnMultiplicity h) σ μ
  rw [hw, finrank_comap_subtype, ← flagTableauCharacter_eq_key] at hc
  have hcount : (toLaurent (flagTableauCharacter h σ)).coeff μ = chainCount h {σ} μ := by
    rw [chainSet_singleton_filter, flagTableauCharacter, map_sum, AddMonoidAlgebra.coeff_sum,
      Finset.sum_apply']
    have hterm : ∀ T : (j : Fin d) → FlagMinorRowSet (h j),
        (toLaurent (if HasFlagDefiningChain h T σ then compositionMonomial (flagTupleWeight h T)
          else 0)).coeff μ =
          if HasFlagDefiningChain h T σ ∧ tupleWeight h T = μ then 1 else 0 := by
      intro T
      by_cases hT : HasFlagDefiningChain h T σ
      · simp only [hT, ite_true, coeff_compositionMonomial_tuple, true_and]
      · simp [hT]
    simp only [hterm]
    rw [Finset.sum_boole]
  exact_mod_cast hc.trans hcount

/-! ### The induction over Bruhat ideals -/

/-- `I` is a lower set for Bruhat order: a union of Schubert varieties `X_I`. -/
def BruhatLower (I : Finset (FinPermutation n)) : Prop := ∀ w ∈ I, ∀ v, v ≤ᴮ w → v ∈ I

theorem demazureUnion_erase_sup (m : ColumnShape n) {I : Finset (FinPermutation n)}
    {σ : FinPermutation n} (hσ : σ ∈ I) :
    demazureUnion m I = demazureUnion m (I.erase σ) ⊔ demazureUnion m {σ} := by
  apply le_antisymm
  · refine (demazureUnion_le_iff m I _).mpr fun w hw => ?_
    by_cases hwσ : w = σ
    · subst hwσ
      exact (flagDemazure_le_demazureUnion m (Finset.mem_singleton_self w)).trans le_sup_right
    · exact (flagDemazure_le_demazureUnion m (Finset.mem_erase.mpr ⟨hwσ, hw⟩)).trans le_sup_left
  · exact sup_le (demazureUnion_mono m fun w hw =>
        ⟨w, Finset.mem_of_mem_erase hw, strongBruhat_refl w⟩)
      (demazureUnion_mono m fun w hw => ⟨w, (Finset.mem_singleton.mp hw) ▸ hσ, strongBruhat_refl w⟩)

theorem schubertBoundary_bruhatLower (σ : FinPermutation n) :
    BruhatLower (schubertBoundary σ) := by
  intro τ hτ v hv
  rw [mem_schubertBoundary] at hτ ⊢
  refine ⟨strongBruhat_trans hv hτ.1, fun hvσ => hτ.2 ?_⟩
  subst hvσ
  exact strongBruhat_antisymm hτ.1 hv

theorem chainCount_eq_zero_of_not_mem (h : Fin d → Fin n) (S : Finset (FinPermutation n))
    (μ : Weight n) (hμ : μ ∉ (chainSet h S).image (tupleWeight h)) : chainCount h S μ = 0 := by
  classical
  unfold chainCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro T hT hTμ
  exact hμ (Finset.mem_image.mpr ⟨T, hT, hTμ⟩)

/-- **The character of a sum of Demazure modules over a Bruhat ideal.** -/
theorem finrank_demazureUnion_inf_eq (h : Fin d → Fin n) (I : Finset (FinPermutation n))
    (hI : BruhatLower I) (μ : Weight n) :
    Module.finrank ℂ (demazureUnion (columnMultiplicity h) I ⊓ ambientWeight μ :
      Submodule ℂ (MatrixPolynomial n)) = chainCount h I μ := by
  classical
  induction I using Finset.strongInduction generalizing μ with
  | H I ih =>
  -- the upper bound, for every weight
  have hupper : ∀ ν, Module.finrank ℂ (demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν :
      Submodule ℂ (MatrixPolynomial n)) ≤ chainCount h I ν := by
    intro ν
    rcases I.eq_empty_or_nonempty with hI0 | hne
    · subst hI0
      rw [demazureUnion_empty, bot_inf_eq, finrank_bot]
      exact Nat.zero_le _
    obtain ⟨σ, hσI, hσmax⟩ := Finset.exists_max_image I FinPermutation.length hne
    have hmax : ∀ τ ∈ I, σ ≤ᴮ τ → τ = σ := fun τ hτ hστ =>
      (eq_of_strongBruhatLE_of_length_eq hστ
        (le_antisymm (length_le_of_strongBruhatLE hστ) (hσmax τ hτ))).symm
    let I' := I.erase σ
    let J := schubertBoundary σ
    have hI' : BruhatLower I' := by
      intro w hw v hv
      refine Finset.mem_erase.mpr ⟨fun hvσ => ?_, hI w (Finset.mem_of_mem_erase hw) v hv⟩
      subst hvσ
      exact (Finset.ne_of_mem_erase hw) (hmax w (Finset.mem_of_mem_erase hw) hv)
    have hJI' : J ⊆ I' := by
      intro τ hτ
      rw [mem_schubertBoundary] at hτ
      exact Finset.mem_erase.mpr ⟨hτ.2, hI σ hσI τ hτ.1⟩
    have hI'I : I' ⊂ I := Finset.erase_ssubset hσI
    have hJI : J ⊂ I := lt_of_le_of_lt hJI' hI'I
    -- dimensions
    have hsup := sup_inf_ambientWeight (demazureUnion (columnMultiplicity h) I')
        (demazureUnion (columnMultiplicity h) {σ})
      (demazureUnion_torus_mem (columnMultiplicity h) I')
          (demazureUnion_torus_mem (columnMultiplicity h) {σ}) ν
    rw [← demazureUnion_erase_sup (columnMultiplicity h) hσI] at hsup
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (demazureUnion (columnMultiplicity h) I' ⊓ ambientWeight ν)
          (demazureUnion (columnMultiplicity h) {σ} ⊓ ambientWeight ν)
    rw [← hsup] at hdim
    have hA := ih I' hI'I hI' ν
    have hB : Module.finrank ℂ (demazureUnion (columnMultiplicity h) {σ} ⊓ ambientWeight ν :
        Submodule ℂ (MatrixPolynomial n)) = chainCount h {σ} ν := by
      rw [demazureUnion_singleton]; exact finrank_flagDemazure_inf h σ ν
    have hJ := ih J hJI (schubertBoundary_bruhatLower σ) ν
    have hJle : demazureUnion (columnMultiplicity h) J ⊓ ambientWeight ν ≤
        (demazureUnion (columnMultiplicity h) I' ⊓ ambientWeight ν) ⊓
            (demazureUnion (columnMultiplicity h) {σ} ⊓ ambientWeight ν) :=
      le_inf (inf_le_inf_right _ (demazureUnion_mono (columnMultiplicity h) fun τ hτ =>
          ⟨τ, hJI' hτ, strongBruhat_refl τ⟩))
        (inf_le_inf_right _ (demazureUnion_mono (columnMultiplicity h) fun τ hτ =>
          ⟨σ, Finset.mem_singleton_self σ, (mem_schubertBoundary.mp hτ).1⟩))
    have hJfin := Submodule.finrank_mono hJle
    -- the counting identity
    have hcount : chainCount h I ν + chainCount h J ν = chainCount h I' ν + chainCount h {σ} ν := by
      unfold chainCount
      have hunion : (chainSet h I).filter (fun T => tupleWeight h T = ν) =
          (chainSet h I').filter (fun T => tupleWeight h T = ν) ∪
            (chainSet h {σ}).filter (fun T => tupleWeight h T = ν) := by
        ext T
        simp only [Finset.mem_union, Finset.mem_filter, mem_chainSet, Finset.mem_singleton,
          exists_eq_left]
        constructor
        · rintro ⟨⟨w, hw, hc⟩, hT⟩
          by_cases hwσ : w = σ
          · subst hwσ; exact Or.inr ⟨hc, hT⟩
          · exact Or.inl ⟨⟨w, Finset.mem_erase.mpr ⟨hwσ, hw⟩, hc⟩, hT⟩
        · rintro (⟨⟨w, hw, hc⟩, hT⟩ | ⟨hc, hT⟩)
          · exact ⟨⟨w, Finset.mem_of_mem_erase hw, hc⟩, hT⟩
          · exact ⟨⟨σ, hσI, hc⟩, hT⟩
      have hinter : (chainSet h I').filter (fun T => tupleWeight h T = ν) ∩
          (chainSet h {σ}).filter (fun T => tupleWeight h T = ν) =
            (chainSet h J).filter (fun T => tupleWeight h T = ν) := by
        ext T
        simp only [Finset.mem_inter, Finset.mem_filter, mem_chainSet, Finset.mem_singleton,
          exists_eq_left]
        constructor
        · rintro ⟨⟨⟨τ, hτ, hcτ⟩, hT⟩, hcσ, -⟩
          obtain ⟨κ, hκ⟩ := exists_rightKey h T ⟨σ, hcσ⟩
          have hκτ := (hκ τ).mp hcτ
          have hκσ := (hκ σ).mp hcσ
          refine ⟨⟨κ, mem_schubertBoundary.mpr ⟨hκσ, fun hκeq => ?_⟩, (hκ κ).mpr
            (strongBruhat_refl κ)⟩, hT⟩
          subst hκeq
          exact (Finset.ne_of_mem_erase hτ) (hmax τ (Finset.mem_of_mem_erase hτ) hκτ)
        · rintro ⟨⟨τ, hτ, hcτ⟩, hT⟩
          exact ⟨⟨⟨τ, hJI' hτ, hcτ⟩, hT⟩, hcτ.mono (mem_schubertBoundary.mp hτ).1, hT⟩
      rw [hunion, ← hinter, Finset.card_union_add_card_inter]
    omega
  -- the lower bound, and equality in every weight
  let F := (chainSet h I).image (tupleWeight h)
  have hzero : ∀ ν, ν ∉ F → demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν = ⊥ := by
    intro ν hν
    have := hupper ν
    rw [chainCount_eq_zero_of_not_mem h I ν hν] at this
    exact Submodule.finrank_eq_zero.mp (Nat.le_zero.mp this)
  have hle : demazureUnion (columnMultiplicity h) I ≤ ⨆ ν ∈ F,
      demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν := by
    refine (le_iSup_inf_ambientWeight _ (demazureUnion_torus_mem (columnMultiplicity h) I)).trans
        (iSup_le fun ν => ?_)
    by_cases hν : ν ∈ F
    · exact le_biSup (fun ν => demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν) hν
    · rw [hzero ν hν]; exact bot_le
  have : FiniteDimensional ℂ (⨆ ν ∈ F, demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν :
      Submodule ℂ (MatrixPolynomial n)) :=
    Submodule.finiteDimensional_of_le (iSup₂_le fun _ _ => inf_le_left)
  have htotal : (chainSet h I).card ≤ ∑ ν ∈ F, Module.finrank ℂ
      (demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν : Submodule ℂ
          (MatrixPolynomial n)) :=
    (card_chainSet_le_finrank h I).trans ((Submodule.finrank_mono hle).trans
      (finrank_biSup_le (demazureUnion (columnMultiplicity h) I) _ (fun _ => inf_le_left) F))
  have hsumc : ∑ ν ∈ F, chainCount h I ν = (chainSet h I).card :=
    (Finset.card_eq_sum_card_image (tupleWeight h) (chainSet h I)).symm
  have heq : ∑ ν ∈ F, Module.finrank ℂ (demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν :
      Submodule ℂ (MatrixPolynomial n)) = ∑ ν ∈ F, chainCount h I ν :=
    le_antisymm (Finset.sum_le_sum fun ν _ => hupper ν) (hsumc ▸ htotal)
  by_cases hμ : μ ∈ F
  · exact (Finset.sum_eq_sum_iff_of_le fun ν _ => hupper ν).mp heq μ hμ
  · rw [hzero μ hμ, finrank_bot, chainCount_eq_zero_of_not_mem h I μ hμ]

/-- The torus character of `D_I`, for a Bruhat ideal `I`. -/
theorem demazureUnion_hasTorusCharacter (h : Fin d → Fin n) (I : Finset (FinPermutation n))
    (hI : BruhatLower I) :
    HasTorusCharacter (demazureUnionModule (columnMultiplicity h) I).torus
        (chainCharacter h I) := by
  intro μ
  change (Module.finrank ℂ (torusWeightSpace (restrictTorus (polynomialTorus n)
    (demazureUnion (columnMultiplicity h) I) (demazureUnion_torus_mem _ I)) μ) : ℤ) = _
  rw [torusWeightSpace_restrictTorus, finrank_comap_subtype, coeff_chainCharacter,
    finrank_demazureUnion_inf_eq h I hI μ]

theorem finrank_demazureUnion_eq (h : Fin d → Fin n) (I : Finset (FinPermutation n))
    (hI : BruhatLower I) :
    Module.finrank ℂ (demazureUnion (columnMultiplicity h) I) = (chainSet h I).card := by
  classical
  refine le_antisymm ?_ (card_chainSet_le_finrank h I)
  let F := (chainSet h I).image (tupleWeight h)
  have hle : demazureUnion (columnMultiplicity h) I ≤
      ⨆ ν ∈ F, demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν := by
    refine (le_iSup_inf_ambientWeight _ (demazureUnion_torus_mem _ I)).trans (iSup_le fun ν => ?_)
    by_cases hν : ν ∈ F
    · exact le_biSup (fun ν => demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν) hν
    · have := finrank_demazureUnion_inf_eq h I hI ν
      rw [chainCount_eq_zero_of_not_mem h I ν hν] at this
      rw [Submodule.finrank_eq_zero.mp this]
      exact bot_le
  have : FiniteDimensional ℂ (⨆ ν ∈ F, demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν :
      Submodule ℂ (MatrixPolynomial n)) :=
    Submodule.finiteDimensional_of_le (iSup₂_le fun _ _ => inf_le_left)
  calc Module.finrank ℂ (demazureUnion (columnMultiplicity h) I)
      ≤ ∑ ν ∈ F, Module.finrank ℂ (demazureUnion (columnMultiplicity h) I ⊓ ambientWeight ν :
          Submodule ℂ (MatrixPolynomial n)) :=
        (Submodule.finrank_mono hle).trans (finrank_biSup_le _ _ (fun _ => inf_le_left) F)
    _ = ∑ ν ∈ F, chainCount h I ν :=
        Finset.sum_congr rfl fun ν _ => finrank_demazureUnion_inf_eq h I hI ν
    _ = (chainSet h I).card := (Finset.card_eq_sum_card_image (tupleWeight h) (chainSet h I)).symm

/-- **Intersections.** For Bruhat ideals `J` and `K`, `D_J ∩ D_K = D_{J ∩ K}`. -/
theorem demazureUnion_inf (h : Fin d → Fin n) {J K : Finset (FinPermutation n)}
    (hJ : BruhatLower J) (hK : BruhatLower K) :
    demazureUnion (columnMultiplicity h) J ⊓ demazureUnion (columnMultiplicity h) K =
      demazureUnion (columnMultiplicity h) (J ∩ K) := by
  classical
  let m := columnMultiplicity h
  have hJK : BruhatLower (J ∩ K) := fun w hw v hv =>
    Finset.mem_inter.mpr ⟨hJ w (Finset.mem_inter.mp hw).1 v hv,
        hK w (Finset.mem_inter.mp hw).2 v hv⟩
  have hJuK : BruhatLower (J ∪ K) := by
    intro w hw v hv
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union.mpr (Or.inl (hJ w hw v hv))
    · exact Finset.mem_union.mpr (Or.inr (hK w hw v hv))
  have hle : demazureUnion m (J ∩ K) ≤ demazureUnion m J ⊓ demazureUnion m K :=
    le_inf (demazureUnion_mono m fun w hw => ⟨w, (Finset.mem_inter.mp hw).1, strongBruhat_refl w⟩)
      (demazureUnion_mono m fun w hw => ⟨w, (Finset.mem_inter.mp hw).2, strongBruhat_refl w⟩)
  have hsup : demazureUnion m J ⊔ demazureUnion m K = demazureUnion m (J ∪ K) := by
    apply le_antisymm
    · exact sup_le (demazureUnion_mono m fun w hw => ⟨w, Finset.mem_union_left K hw,
        strongBruhat_refl w⟩) (demazureUnion_mono m fun w hw => ⟨w, Finset.mem_union_right J hw,
        strongBruhat_refl w⟩)
    · refine (demazureUnion_le_iff m _ _).mpr fun w hw => ?_
      rcases Finset.mem_union.mp hw with hw | hw
      · exact (flagDemazure_le_demazureUnion m hw).trans le_sup_left
      · exact (flagDemazure_le_demazureUnion m hw).trans le_sup_right
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (demazureUnion m J) (demazureUnion m K)
  rw [hsup, finrank_demazureUnion_eq h _ hJuK, finrank_demazureUnion_eq h _ hJ,
    finrank_demazureUnion_eq h _ hK] at hdim
  have hunion : chainSet h (J ∪ K) = chainSet h J ∪ chainSet h K := by
    ext T
    simp only [mem_chainSet, Finset.mem_union]
    constructor
    · rintro ⟨w, hw | hw, hc⟩
      · exact Or.inl ⟨w, hw, hc⟩
      · exact Or.inr ⟨w, hw, hc⟩
    · rintro (⟨w, hw, hc⟩ | ⟨w, hw, hc⟩)
      · exact ⟨w, Or.inl hw, hc⟩
      · exact ⟨w, Or.inr hw, hc⟩
  have hinter : chainSet h J ∩ chainSet h K = chainSet h (J ∩ K) := by
    ext T
    simp only [mem_chainSet, Finset.mem_inter]
    constructor
    · rintro ⟨⟨w, hw, hc⟩, ⟨w', hw', hc'⟩⟩
      obtain ⟨κ, hκ⟩ := exists_rightKey h T ⟨w, hc⟩
      exact ⟨κ, ⟨hJ w hw κ ((hκ w).mp hc), hK w' hw' κ ((hκ w').mp hc')⟩,
        (hκ κ).mpr (strongBruhat_refl κ)⟩
    · rintro ⟨w, ⟨hwJ, hwK⟩, hc⟩
      exact ⟨⟨w, hwJ, hc⟩, ⟨w, hwK, hc⟩⟩
  have hcard := Finset.card_union_add_card_inter (chainSet h J) (chainSet h K)
  rw [← hunion, hinter] at hcard
  have hfin : Module.finrank ℂ (demazureUnion m J ⊓ demazureUnion m K :
      Submodule ℂ (MatrixPolynomial n)) = Module.finrank ℂ (demazureUnion m (J ∩ K)) := by
    rw [finrank_demazureUnion_eq h _ hJK]
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin.symm).symm

end

end Demazure.SchubertUnions
