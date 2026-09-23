import Schubert.RS.Representation.Sl2AdjointWeyl
import Schubert.RS.Representation.EnvelopingGrading

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 2000000

theorem exp_mem_of_stable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module ℚ M]
    (D : Module.End ℂ M) (hD : IsNilpotent D) (S : Submodule ℂ M)
    (hs : ∀ x∈S, D x∈S) {x : M} (hx : x∈S) : IsNilpotent.exp D x∈S := by
  have hp : ∀ k, (D^k) x∈S := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih => rw [pow_succ',Module.End.mul_apply]; exact hs _ ih
  obtain ⟨k,hk⟩ := hD
  rw [IsNilpotent.exp_eq_sum hk,LinearMap.sum_apply]
  apply S.sum_mem
  intro j hj
  change ((j.factorial:ℚ)⁻¹) • (D^j) x∈S
  have hq : ((j.factorial:ℚ)⁻¹) • (D^j) x = (((j.factorial:ℚ)⁻¹):ℂ) • (D^j) x := by
    simpa using (ratCast_smul_eq ℚ ℂ ((j.factorial:ℚ)⁻¹) ((D^j) x))
  rw [hq]
  exact S.smul_mem _ (hp j)

variable {L M : Type*} [LieRing L] [LieAlgebra ℂ L] {h e f : L} (t : IsSl2Triple h e f)
  [AddCommGroup M] [Module ℂ M] [Module ℚ M]
  [LieRingModule (t.toLieSubalgebra ℂ) M] [LieModule ℂ (t.toLieSubalgebra ℂ) M]
  (hE : IsNilpotent (LieModule.toEnd ℂ _ M (sl2RaisingElement t)))
  (hF : IsNilpotent (LieModule.toEnd ℂ _ M (sl2LoweringElement t)))

theorem nilpotentWeyl_cartan (x : M) :
    ⁅sl2CartanElement t,nilpotentWeylEquiv _ _ hE hF x⁆ =
      -nilpotentWeylEquiv _ _ hE hF ⁅sl2CartanElement t,x⁆ := by
  letI := complexRationalModule (t.toLieSubalgebra ℂ)
  let w := nilpotentWeylEquiv _ _ hE hF
  have hw : w ⁅sl2CartanElement t,x⁆ = ⁅sl2AdjointWeyl t (sl2CartanElement t),w x⁆ :=
    LieModuleHom.weyl_tensor_covariance (LieModule.toModuleHom ℂ (t.toLieSubalgebra ℂ) M)
      (sl2RaisingElement t) (sl2LoweringElement t)
      ⟨3,sl2AdjointE_cube t⟩ ⟨3,sl2AdjointF_cube t⟩ hE hF (sl2CartanElement t) x
  have hh : w ⁅sl2CartanElement t,x⁆ = -⁅sl2CartanElement t,w x⁆ :=
    hw.trans ((congrArg (fun z => ⁅z,w x⁆) (sl2AdjointWeyl_h t)).trans (neg_lie _ _))
  exact (neg_neg _).symm.trans (congrArg Neg.neg hh.symm)

variable [Module.Finite ℂ M] {m : M} {d : ℕ}
  (P : (sl2SubalgebraTriple t).HasPrimitiveVectorWith m (d:ℂ))

theorem fullPrimitive_lowest_line (x : fullPrimitiveModule t P)
    (hx : ⁅sl2CartanElement t,x⁆=-(d:ℂ) • x) :
    x = (fullPrimitiveBasis t P).repr x ⟨d,by omega⟩ • fullPrimitiveBasis t P ⟨d,by omega⟩ := by
  classical
  let b := fullPrimitiveBasis t P
  change x = b.repr x ⟨d,by omega⟩ • b ⟨d,by omega⟩
  apply b.repr.injective
  ext k
  by_cases hk : k=⟨d,by omega⟩
  · subst k
    simp
  · simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,smul_eq_mul,Finsupp.single_apply]
    rw [if_neg (Ne.symm hk),mul_zero]
    have heq := basis_coord_eigenmap b
      (LieModule.toEnd ℂ _ (fullPrimitiveModule t P) (sl2CartanElement t))
      (fun j : Fin (d+1) => (d:ℂ)-2*j.val) (fullPrimitiveBasis_h t P) k x
    change b.repr ⁅sl2CartanElement t,x⁆ k = _ at heq
    rw [hx,map_smul,Finsupp.smul_apply,smul_eq_mul] at heq
    have hn : -(d:ℂ) ≠ (d:ℂ)-2*k.val := by
      intro he
      apply hk
      apply Fin.ext
      have hh : (k.val:ℂ)=(d:ℂ) := by linear_combination he / 2
      exact_mod_cast hh
    have hz : (-(d:ℂ)-((d:ℂ)-2*k.val))*b.repr x k=0 := by rw [sub_mul,heq,sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hn)

include P in
/-- The actual Weyl operator takes a highest vector to a nonzero scalar
multiple of its proved lowest string endpoint. -/
theorem nilpotentWeyl_highest_endpoint :
    ∃ c : ℂ, c≠0 ∧ nilpotentWeylEquiv _ _ hE hF m =
      c • primitiveStringVector (sl2LoweringElement t) m d := by
  let W := fullPrimitiveModule t P
  let w := nilpotentWeylEquiv _ _ hE hF
  have hm : m∈W := by
    change m∈primitiveStringSpan (sl2LoweringElement t) m d
    simpa only [Fin.val_zero,primitiveStringVector_zero] using
      (primitiveStringVector_mem (f := sl2LoweringElement t) (m := m) (d := d) (0 : Fin (d+1)))
  have he (x : M) (hx : x∈W) : (LieModule.toEnd ℂ _ M (sl2RaisingElement t)) x∈W := W.lie_mem hx
  have hf (x : M) (hx : x∈W) : (-(LieModule.toEnd ℂ _ M (sl2LoweringElement t))) x∈W :=
    W.toSubmodule.neg_mem (W.lie_mem hx)
  have hy : w m∈W :=
    exp_mem_of_stable _ hE W.toSubmodule he
      (exp_mem_of_stable _ hF.neg W.toSubmodule hf (exp_mem_of_stable _ hE W.toSubmodule he hm))
  let y : W := ⟨w m,hy⟩
  have hh : ⁅sl2CartanElement t,y⁆=-(d:ℂ) • y := by
    apply Subtype.ext
    change ⁅sl2CartanElement t,w m⁆=-(d:ℂ) • w m
    rw [nilpotentWeyl_cartan t hE hF,P.lie_h,map_smul,neg_smul]
  let c := (fullPrimitiveBasis t P).repr y ⟨d,by omega⟩
  have hval : w m=c • primitiveStringVector (sl2LoweringElement t) m d :=
    (congrArg Subtype.val (fullPrimitive_lowest_line t P y hh)).trans
      (congrArg (c • ·) (fullPrimitiveBasis_val t P ⟨d,by omega⟩))
  refine ⟨c,?_,hval⟩
  intro hc
  apply P.ne_zero
  apply w.injective
  exact hval.trans ((congrArg (· • primitiveStringVector (sl2LoweringElement t) m d) hc).trans
    ((zero_smul ℂ _).trans w.map_zero.symm))

end
end Schubert.RS.Representation
