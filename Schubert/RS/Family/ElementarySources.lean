import Schubert.RS.Family.HallChoices
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-! The paper's elementary-symmetric source polynomials. Variables may be
arbitrary elements of a commutative ring. -/

namespace Schubert.RS.Family
noncomputable section
variable {m p : ℕ} {R : Type*} [CommRing R]

/-- The paper's sum of products of elementary symmetric polynomials. -/
def earlyLatePolynomial (p : ℕ) (early late : Fin m → R) : R :=
  ∑ h : Fin (p+1), (Finset.univ.val.map early).esymm h.val *
    (Finset.univ.val.map late).esymm (2*p-1-h.val)

abbrev SourceDegreeChoices (m p : ℕ) :=
  (h : Fin (p+1)) × ({e : Finset (Fin m) // e.card=h.val} ×
    {l : Finset (Fin m) // l.card=2*p-1-h.val})

def sourceDegreeChoice (hp : 0<p) (s : SourceDegreeChoices m p) : PairedChoice m p :=
  ⟨(s.2.1.val,s.2.2.val),by
    have hh := s.1.isLt
    rw [s.2.1.property,s.2.2.property]
    constructor <;> omega⟩

theorem sourceDegreeChoice_bijective (hp : 0<p) :
    Function.Bijective (sourceDegreeChoice (m:=m) hp) := by
  constructor
  · rintro ⟨h,e,l⟩ ⟨k,f,g⟩ heq
    have he := congrArg (fun s : PairedChoice m p => s.val.1) heq
    have hl := congrArg (fun s : PairedChoice m p => s.val.2) heq
    change e.val=f.val at he
    change l.val=g.val at hl
    have hk : h=k := Fin.ext (by rw [← e.property,← f.property,he])
    subst k
    exact congrArg (Sigma.mk h) (Prod.ext (Subtype.ext he) (Subtype.ext hl))
  · intro s
    refine ⟨⟨⟨s.val.1.card,by have hb:=s.property.2; omega⟩,
      ⟨s.val.1,rfl⟩,⟨s.val.2,by change s.val.2.card=2*p-1-s.val.1.card; have hd:=s.property.1; omega⟩⟩,?_⟩
    rfl

theorem esymm_sum_fixed (x : Fin m → R) (k : ℕ) :
    (Finset.univ.val.map x).esymm k =
      ∑ s : {s : Finset (Fin m) // s.card=k}, ∏ i ∈ s.val,x i := by
  classical
  rw [Finset.esymm_map_val]
  exact Finset.sum_subtype _ (by simp) _

theorem earlyLatePolynomial_selections (hp : 0<p) (early late : Fin m → R) :
    earlyLatePolynomial p early late =
      ∑ s : PairedChoice m p,(∏ i ∈ s.val.1,early i)*∏ i ∈ s.val.2,late i := by
  classical
  unfold earlyLatePolynomial
  simp_rw [esymm_sum_fixed,Finset.sum_mul,Finset.mul_sum]
  have he := Fintype.sum_bijective (sourceDegreeChoice (m:=m) hp)
    (sourceDegreeChoice_bijective hp)
    (fun s => (∏ i ∈ s.2.1.val,early i)*∏ i ∈ s.2.2.val,late i)
    (fun s => (∏ i ∈ s.val.1,early i)*∏ i ∈ s.val.2,late i)
    (fun _ => rfl)
  simpa only [Fintype.sum_sigma,Fintype.sum_prod_type] using he

theorem hallPolynomial_elementary (hm : 0<m) (hp : 0<p) (slot : Slot m → R) :
    hallPolynomial (hallHeights hm p) slot =
      earlyLatePolynomial p (fun i => slot (slotRight i)) (fun i => slot (slotLeft i)) := by
  rw [earlyLatePolynomial_selections hp,hallPolynomial_paired_choices]

theorem earlyLatePolynomial_permute_late (p : ℕ) (early late : Fin m → R)
    (σ : Equiv.Perm (Fin m)) :
    earlyLatePolynomial p early (fun i => late (σ i)) = earlyLatePolynomial p early late := by
  have hl : Finset.univ.val.map (fun i => late (σ i)) = Finset.univ.val.map late := by
    change Finset.univ.val.map (late ∘ σ) = _
    rw [← Multiset.map_map,Multiset.map_univ_val_equiv]
  simp only [earlyLatePolynomial,hl]

theorem map_earlyLatePolynomial {S : Type*} [CommRing S] (f : R →+* S)
    (hp : 0<p) (early late : Fin m → R) :
    f (earlyLatePolynomial p early late) =
      earlyLatePolynomial p (fun i => f (early i)) (fun i => f (late i)) := by
  simp only [earlyLatePolynomial_selections hp,map_sum,map_mul,map_prod]

end
end Schubert.RS.Family
