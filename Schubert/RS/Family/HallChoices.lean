import Schubert.RS.Family.Slots
import Schubert.RS.DoubleSourceExtraction
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Fin

/-! Complete Hall extraction for a source of size 2p-1: at most p early
targets may be used. This is valid for both unequal source classes. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p : ℕ}

def hallHeights (hm : 0<m) (p : ℕ) (i : Fin (2*p-1)) : Slot m :=
  ⟨if i.val<p-1 then m-1 else 2*m-1,by split_ifs <;> omega⟩

theorem hallHeights_monotone (hm : 0<m) (p : ℕ) :
    Monotone (fun i => (hallHeights hm p i).val) := by
  intro i j hij
  have he : i.val≤j.val := hij
  simp only [hallHeights]
  split_ifs <;> omega

abbrev HallChoice (m p : ℕ) := {s : Finset (Slot m) //
  s.card=2*p-1 ∧ p-1≤(s.filter (fun j => j.val<m)).card}

instance (m p : ℕ) : Fintype (HallChoice m p) := Fintype.ofFinite _

def strictSlot (hm : 0<m) (r : HallLattice.StrictHeights (hallHeights hm p))
    (i : Fin (2*p-1)) : Slot m :=
  ⟨(r.val i).val,by have h:=(r.val i).isLt; have hy:=(hallHeights hm p i).isLt; omega⟩

theorem strictSlot_strictMono (hm : 0<m) (r : HallLattice.StrictHeights (hallHeights hm p)) :
    StrictMono (strictSlot hm r) := r.property

theorem image_filter_card {d : ℕ} (f : Fin d → Slot m) (hf : Function.Injective f)
    (s : Finset (Fin d)) :
    ((s.image f).filter (fun j => j.val<m)).card=
      (s.filter (fun i => (f i).val<m)).card := by
  rw [Finset.filter_image,Finset.card_image_of_injective _ hf]

def strictHeightChoice (hm : 0<m) (r : HallLattice.StrictHeights (hallHeights hm p)) :
    HallChoice m p :=
  ⟨Finset.univ.image (strictSlot hm r),by
    constructor
    · rw [Finset.card_image_of_injective _ (strictSlot_strictMono hm r).injective]
      exact Finset.card_fin _
    · rw [image_filter_card _ (strictSlot_strictMono hm r).injective]
      have hsub : Finset.univ.filter (fun i : Fin (2*p-1) => i.val<p-1) ⊆
          Finset.univ.filter (fun i => (strictSlot hm r i).val<m) := by
        intro i hi
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
        have hr:=(r.val i).isLt
        have hy : (hallHeights hm p i).val=m-1 := by simp [hallHeights,hi]
        change (r.val i).val<m
        omega
      have hc : (Finset.univ.filter (fun i : Fin (2*p-1) => i.val<p-1)).card=p-1 := by
        rw [Fin.card_filter_val_lt,Nat.min_eq_right (by omega)]
      rw [← hc]
      exact Finset.card_le_card hsub⟩

theorem choice_order_bound (hm : 0<m) (s : HallChoice m p) (i : Fin (2*p-1)) :
    (s.val.orderEmbOfFin s.property.1 i).val≤(hallHeights hm p i).val := by
  let f:=s.val.orderEmbOfFin s.property.1
  have hc : p-1≤(Finset.univ.filter (fun i => (f i).val<m)).card := by
    rw [← image_filter_card f f.injective,Finset.image_orderEmbOfFin_univ]
    exact s.property.2
  simp only [hallHeights]
  split_ifs with hi
  · change (f i).val≤m-1
    have he : (f i).val<m :=
      (Tuple.lt_card_lt_iff_apply_lt_of_monotone
        (show Monotone (fun i => (f i).val) from f.monotone)).mp (by omega)
    omega
  · change (f i).val≤2*m-1
    have he:=(f i).isLt
    omega

def choiceStrictHeight (hm : 0<m) (s : HallChoice m p) :
    HallLattice.StrictHeights (hallHeights hm p) :=
  ⟨fun i => ⟨(s.val.orderEmbOfFin s.property.1 i).val,
      Nat.lt_succ_of_le (choice_order_bound hm s i)⟩,
    (s.val.orderEmbOfFin s.property.1).strictMono⟩

def hallChoiceEquiv (hm : 0<m) : HallLattice.StrictHeights (hallHeights hm p) ≃ HallChoice m p where
  toFun:=strictHeightChoice hm
  invFun:=choiceStrictHeight hm
  left_inv r:=by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have he:=Finset.orderEmbOfFin_unique (strictHeightChoice hm r).property.1
      (fun j => Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
      (strictSlot_strictMono hm r)
    exact (congrArg (fun f => (f i).val) he).symm
  right_inv s:=by
    apply Subtype.ext
    change Finset.univ.image (s.val.orderEmbOfFin s.property.1)=s.val
    exact Finset.image_orderEmbOfFin_univ _ _

theorem hallPolynomial_choices (hm : 0<m) {R : Type*} [CommRing R] (slot : Slot m → R) :
    hallPolynomial (hallHeights hm p) slot=∑ s : HallChoice m p,∏ j ∈ s.val,slot j := by
  classical
  rw [← (hallChoiceEquiv hm).sum_comp (fun s => ∏ j ∈ s.val,slot j)]
  apply Finset.sum_congr rfl
  intro r _
  change (∏ i : Fin (2*p-1),slot (strictSlot hm r i))=
    ∏ j ∈ Finset.univ.image (strictSlot hm r),slot j
  exact (Finset.prod_image (fun i _ j _ h => (strictSlot_strictMono hm r).injective h)).symm

theorem paired_choice_iff (hm : 0<m) (s : Finset (Fin m) × Finset (Fin m)) :
    (s.1.card+s.2.card=2*p-1 ∧ s.1.card≤p) ↔
      ((pairSlots hm s).card=2*p-1 ∧ p-1≤((pairSlots hm s).filter (fun j => j.val<m)).card) := by
  rw [pairSlots_card,pairSlots_low_card]
  omega

def pairedChoiceEquiv (hm : 0<m) : PairedChoice m p ≃ HallChoice m p :=
  Equiv.subtypeEquiv (pairSlots hm) (paired_choice_iff hm)

theorem paired_choice_weight (hm : 0<m) {R : Type*} [CommRing R]
    (s : PairedChoice m p) (slot : Slot m → R) :
    (∏ j ∈ (pairedChoiceEquiv hm s).val,slot j)=
      (∏ i ∈ s.val.1,slot (slotRight i))*∏ i ∈ s.val.2,slot (slotLeft i) := by
  change (∏ j ∈ pairSlots hm s.val,slot j)=_
  rw [pairSlots_apply,Finset.prod_map,Finset.prod_disjSum]
  rfl

theorem hallPolynomial_paired_choices (hm : 0<m) {R : Type*} [CommRing R]
    (slot : Slot m → R) :
    hallPolynomial (hallHeights hm p) slot=∑ s : PairedChoice m p,
      (∏ i ∈ s.val.1,slot (slotRight i))*∏ i ∈ s.val.2,slot (slotLeft i) := by
  rw [hallPolynomial_choices,← (pairedChoiceEquiv hm).sum_comp]
  exact Finset.sum_congr rfl (fun s _ => paired_choice_weight hm s slot)

end
end Schubert.RS.Family
