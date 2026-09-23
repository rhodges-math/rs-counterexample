import Schubert.RS.Sl2FullPrimitive
import Mathlib.Algebra.Lie.TensorProduct

namespace Schubert.RS.Representation
noncomputable section
open LieModule Module

def terminalStringScale (d : ℕ) : ℕ → ℂ
  | 0 => 1
  | k+1 => ((k+1:ℕ):ℂ)*((d:ℂ)-k)*terminalStringScale d k

theorem terminalStringScale_ne_zero (d k : ℕ) (hk : k≤d) : terminalStringScale d k≠0 := by
  induction k with
  | zero => simp [terminalStringScale]
  | succ k ih =>
      rw [terminalStringScale]
      apply mul_ne_zero
      · apply mul_ne_zero
        · exact_mod_cast Nat.succ_ne_zero k
        · apply sub_ne_zero.mpr
          intro he
          have hdk : d=k := by exact_mod_cast he
          omega
      · exact ih (by omega)

theorem raisingString_h {L N : Type*} [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup N] [Module ℂ N] [LieRingModule L N] [LieModule ℂ L N]
    {h e f : L} (t : IsSl2Triple h e f) (p : N) (ξ : ℂ)
    (hp : ⁅h,p⁆=ξ • p) (k : ℕ) :
    ⁅h,primitiveStringVector e p k⁆=(ξ+2*k) • primitiveStringVector e p k := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
      rw [primitiveStringVector_succ,leibniz_lie,t.lie_h_e_smul (R := ℂ),smul_lie,
        ih,lie_smul,← add_smul]
      congr 1
      push_cast
      ring

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
  {h e f : L} (t : IsSl2Triple h e f)
  {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule (t.toLieSubalgebra ℂ) M] [LieModule ℂ (t.toLieSubalgebra ℂ) M]
  [Module.Finite ℂ M] {m : M} {d : ℕ}
  (P : (sl2SubalgebraTriple t).HasPrimitiveVectorWith m (d:ℂ))
  {N : Type*} [AddCommGroup N] [Module ℂ N]
  [LieRingModule (t.toLieSubalgebra ℂ) N] [LieModule ℂ (t.toLieSubalgebra ℂ) N]

/-- The reversed and normalized raising string is a twisted Borel map from
the full highest-weight-d module. No semisimplicity is used. -/
def terminalStringMap (p : N) : fullPrimitiveModule t P →ₗ[ℂ] N :=
  (fullPrimitiveBasis t P).constr ℂ (fun k => terminalStringScale d k.val •
    primitiveStringVector (sl2RaisingElement t) p (d-k.val))

theorem terminalStringMap_basis (p : N) (k : Fin (d+1)) :
    terminalStringMap t P p (fullPrimitiveBasis t P k)=terminalStringScale d k.val •
      primitiveStringVector (sl2RaisingElement t) p (d-k.val) :=
  (fullPrimitiveBasis t P).constr_basis ℂ _ k

theorem terminalStringMap_ne_zero (p : N)
    (hp : primitiveStringVector (sl2RaisingElement t) p d≠0) :
    terminalStringMap t P p≠0 := by
  intro hz
  have hh := LinearMap.congr_fun hz (fullPrimitiveBasis t P 0)
  rw [terminalStringMap_basis] at hh
  apply hp
  simpa [terminalStringScale] using hh

theorem terminalStringMap_e (p : N)
    (hp : primitiveStringVector (sl2RaisingElement t) p (d+1)=0)
    (x : fullPrimitiveModule t P) :
    terminalStringMap t P p ⁅sl2RaisingElement t,x⁆=
      ⁅sl2RaisingElement t,terminalStringMap t P p x⁆ := by
  have hh : (terminalStringMap t P p).comp
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) _ (sl2RaisingElement t))=
      (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) N (sl2RaisingElement t)).comp
        (terminalStringMap t P p) := by
    apply (fullPrimitiveBasis t P).ext
    rintro ⟨k,hk⟩
    change terminalStringMap t P p ⁅sl2RaisingElement t,fullPrimitiveBasis t P ⟨k,hk⟩⁆=
      ⁅sl2RaisingElement t,terminalStringMap t P p (fullPrimitiveBasis t P ⟨k,hk⟩)⁆
    cases k with
    | zero =>
        have hk0 : (⟨0,hk⟩ : Fin (d+1))=0 := Fin.ext rfl
        rw [hk0,fullPrimitiveBasis_e_zero,map_zero,terminalStringMap_basis]
        simp only [Fin.val_zero,terminalStringScale,one_smul,Nat.sub_zero,
          ← primitiveStringVector_succ,hp]
    | succ k =>
        rw [fullPrimitiveBasis_e_succ,map_smul,terminalStringMap_basis,
          terminalStringMap_basis,lie_smul,← primitiveStringVector_succ]
        have hdk : d-(k+1)+1=d-k := by omega
        simp only [hdk,terminalStringScale,smul_smul,Nat.cast_add,Nat.cast_one]
  exact LinearMap.congr_fun hh x

theorem terminalStringMap_h (p : N) (ξ : ℂ)
    (hp : ⁅sl2CartanElement t,p⁆=ξ • p) (x : fullPrimitiveModule t P) :
    ⁅sl2CartanElement t,terminalStringMap t P p x⁆=
      terminalStringMap t P p ⁅sl2CartanElement t,x⁆+(ξ+d) • terminalStringMap t P p x := by
  have hh : (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) N (sl2CartanElement t)).comp
      (terminalStringMap t P p)=
      (terminalStringMap t P p).comp
        (LieModule.toEnd ℂ (t.toLieSubalgebra ℂ) _ (sl2CartanElement t))+
          (ξ+d) • terminalStringMap t P p := by
    apply (fullPrimitiveBasis t P).ext
    intro k
    change ⁅sl2CartanElement t,terminalStringMap t P p (fullPrimitiveBasis t P k)⁆=
      terminalStringMap t P p ⁅sl2CartanElement t,fullPrimitiveBasis t P k⁆+
        (ξ+d) • terminalStringMap t P p (fullPrimitiveBasis t P k)
    rw [fullPrimitiveBasis_h,map_smul,terminalStringMap_basis,lie_smul,
      raisingString_h (sl2SubalgebraTriple t) p ξ hp,smul_smul,smul_smul,smul_smul,
      ← add_smul,Nat.cast_sub (by omega : k.val≤d)]
    congr 1
    ring
  exact LinearMap.congr_fun hh x

include P in
/-- Any terminal Borel string lying in a finite integrable module has
nonnegative integral residual highest weight. -/
theorem terminalString_residual_nat [Module.Finite ℂ N] (p : N) (ξ : ℂ)
    (hH : ⁅sl2CartanElement t,p⁆=ξ • p)
    (htop : primitiveStringVector (sl2RaisingElement t) p d≠0)
    (hend : primitiveStringVector (sl2RaisingElement t) p (d+1)=0) :
    ∃ q : ℕ, ξ+d=q := by
  have hμ : ⁅sl2CartanElement t,terminalStringMap t P p⁆=
      (ξ+d) • terminalStringMap t P p := by
    apply LinearMap.ext
    intro x
    simp only [LieHom.lie_apply,LinearMap.smul_apply,terminalStringMap_h t P p ξ hH]
    abel
  have hE : ⁅sl2RaisingElement t,terminalStringMap t P p⁆=0 := by
    apply LinearMap.ext
    intro x
    simp only [LieHom.lie_apply,LinearMap.zero_apply,← terminalStringMap_e t P p hend,sub_self]
  exact (IsSl2Triple.HasPrimitiveVectorWith.mk (t := sl2SubalgebraTriple t)
    (terminalStringMap_ne_zero t P p htop) hμ hE).exists_nat

end
end Schubert.RS.Representation
