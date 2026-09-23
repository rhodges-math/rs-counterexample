import Schubert.RS.PolynomialWeightSpanning

namespace Schubert.RS.Representation
noncomputable section
open scoped BigOperators

def polynomialTorusOnSubmodule {n : ℕ} (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ t p, p∈S → polynomialTorus n t p∈S) (t : DiagonalTorus n) :
    Module.End ℂ S where
  toFun p := ⟨polynomialTorus n t p.val,hS t p.val p.property⟩
  map_add' p q := Subtype.ext ((polynomialTorus n t).map_add p.val q.val)
  map_smul' c p := Subtype.ext ((polynomialTorus n t).map_smul c p.val)

theorem exists_weight_vector_detected {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ (MatrixPolynomial n))
    (hS : ∀ t p, p∈S → polynomialTorus n t p∈S)
    (f : MatrixPolynomial n →ₗ[ℂ] V) (hf : ∃ p∈S, f p≠0) :
    ∃ p∈S, ∃ v : Weight n, (∀ t, polynomialTorus n t p=integerWeightScalar v t • p) ∧ f p≠0 := by
  classical
  by_contra hn
  push Not at hn
  have hle : polynomialWeightSpan S≤LinearMap.ker f := by
    apply Submodule.span_le.mpr
    intro p hp
    obtain ⟨hp,v,hv⟩ := hp
    exact hn p hp v hv
  rw [polynomialWeightSpan_eq S hS] at hle
  obtain ⟨p,hp,hfp⟩ := hf
  exact hfp (hle hp)

theorem exists_maximal_weight_string {n : ℕ} (a b : Fin n) (hab : a≠b)
    (S : Submodule ℂ (MatrixPolynomial n)) [FiniteDimensional ℂ S] (hS0 : S≠⊥)
    (hE : ∀ p∈S, matrixUnitDerivation a b p∈S)
    (hT : ∀ t p, p∈S → polynomialTorus n t p∈S) :
    ∃ d p, p∈S ∧ ∃ v : Weight n,
      (∀ t, polynomialTorus n t p=integerWeightScalar v t • p) ∧
      derivationIter (matrixUnitDerivation a b) d p≠0 ∧
      (∀ x∈S, derivationIter (matrixUnitDerivation a b) (d+1) x=0) := by
  classical
  let E := matrixUnitOnSubmodule a b S hE
  have hnil : ∃ k, E^k=0 := matrixUnitOnSubmodule_nilpotent a b hab S hE
  haveI : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS0
  have hpos : 0<Nat.find hnil := (Nat.find_pos hnil).mpr (by simp)
  let d := Nat.find hnil-1
  have hd : d+1=Nat.find hnil := by omega
  have hzero : E^(d+1)=0 := by rw [hd]; exact Nat.find_spec hnil
  have hne : E^d≠0 := Nat.find_min hnil (by omega)
  have hex : ∃ p∈S, derivationIter (matrixUnitDerivation a b) d p≠0 := by
    by_contra hn
    push Not at hn
    apply hne
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    change ((matrixUnitOnSubmodule a b S hE^d) p : MatrixPolynomial n)=0
    rw [matrixUnitOnSubmodule_pow]
    exact hn p.val p.property
  obtain ⟨p,hp,v,hv,htop⟩ := exists_weight_vector_detected S hT
    (derivationIter (matrixUnitDerivation a b) d) hex
  refine ⟨d,p,hp,v,hv,htop,?_⟩
  intro x hx
  have hz := congrArg (fun f : Module.End ℂ S => (f ⟨x,hx⟩).val) hzero
  change ((matrixUnitOnSubmodule a b S hE^(d+1)) ⟨x,hx⟩ : MatrixPolynomial n)=0 at hz
  rwa [matrixUnitOnSubmodule_pow] at hz

def matrixUnitStringSpan {n : ℕ} (a b : Fin n) (p : MatrixPolynomial n) (d : ℕ) :
    Submodule ℂ (MatrixPolynomial n) :=
  Submodule.span ℂ (Set.range (fun j : Fin (d+1) => derivationIter (matrixUnitDerivation a b) j.val p))

theorem matrixUnitStringSpan_map {n : ℕ} (a b : Fin n)
    (S : Submodule ℂ (MatrixPolynomial n))
    (hE : ∀ p∈S, matrixUnitDerivation a b p∈S) (p : S) (d : ℕ) :
    (Submodule.span ℂ (Set.range (fun j : Fin (d+1) => (matrixUnitOnSubmodule a b S hE^j.val) p))).map
      S.subtype = matrixUnitStringSpan a b p.val d := by
  rw [Submodule.map_span,← Set.range_comp]
  congr 2
  funext j
  exact matrixUnitOnSubmodule_pow a b S hE j.val p

/-- Split off one maximal homogeneous root string, retaining a torus- and
root-stable complement of strictly smaller dimension. -/
theorem exists_weight_string_complement {n : ℕ} (a b : Fin n) (hab : a≠b)
    (S : Submodule ℂ (MatrixPolynomial n)) [FiniteDimensional ℂ S] (hS0 : S≠⊥)
    (hE : ∀ p∈S, matrixUnitDerivation a b p∈S)
    (hT : ∀ t p, p∈S → polynomialTorus n t p∈S) :
    ∃ d p, p∈S ∧ ∃ v : Weight n,
      (∀ t, polynomialTorus n t p=integerWeightScalar v t • p) ∧
      derivationIter (matrixUnitDerivation a b) d p≠0 ∧
      derivationIter (matrixUnitDerivation a b) (d+1) p=0 ∧
      ∃ K : Submodule ℂ (MatrixPolynomial n), K<S ∧
        Disjoint (matrixUnitStringSpan a b p d) K ∧
        matrixUnitStringSpan a b p d ⊔ K=S ∧
        (∀ x∈K, matrixUnitDerivation a b x∈K) ∧
        (∀ t x, x∈K → polynomialTorus n t x∈K) := by
  classical
  obtain ⟨d,p,hp,v,hv,htop,hzero⟩ := exists_maximal_weight_string a b hab S hS0 hE hT
  obtain ⟨φ,hφ,hφT⟩ := matrixUnit_string_top_functional a b hab p v hv d htop
  let E := matrixUnitOnSubmodule a b S hE
  let pS : S := ⟨p,hp⟩
  let ψ := φ.comp S.subtype
  have hEzero : E^(d+1)=0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((matrixUnitOnSubmodule a b S hE^(d+1)) x : MatrixPolynomial n)=0
    rw [matrixUnitOnSubmodule_pow]
    exact hzero x.val x.property
  have hψ : ∀ j≤d, ψ ((E^j) pS)=if j=d then 1 else 0 := by
    intro j hj
    change φ (((matrixUnitOnSubmodule a b S hE^j) pS : S).val)=_
    rw [matrixUnitOnSubmodule_pow]
    exact hφ j hj
  let C := Submodule.span ℂ (Set.range (fun j : Fin (d+1) => (E^j.val) pS))
  let P := nilpotentStringProjection E pS d ψ
  let K := (LinearMap.ker P).map S.subtype
  have hcompl : IsCompl C (LinearMap.ker P) := nilpotentStringProjection_complement E pS d ψ hEzero hψ
  have hCmap : C.map S.subtype=matrixUnitStringSpan a b p d := matrixUnitStringSpan_map a b S hE pS d
  have hdis : Disjoint (matrixUnitStringSpan a b p d) K := by
    rw [← hCmap]
    exact Submodule.disjoint_map (Submodule.subtype_injective S) hcompl.disjoint
  have hsup : matrixUnitStringSpan a b p d ⊔ K=S := by
    rw [← hCmap,← Submodule.map_sup,hcompl.sup_eq_top,Submodule.map_subtype_top]
  have hKle : K≤S := Submodule.map_subtype_le S _
  have hKlt : K<S := by
    apply lt_of_le_of_ne hKle
    intro he
    have hpC : p∈matrixUnitStringSpan a b p d := Submodule.subset_span ⟨⟨0,by omega⟩,rfl⟩
    have hpK : p∈K := he.symm ▸ hp
    have hp0 : p=0 := (Submodule.disjoint_def.mp hdis) p hpC hpK
    exact htop (by rw [hp0,map_zero])
  refine ⟨d,p,hp,v,hv,htop,hzero p hp,K,hKlt,hdis,hsup,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨E y,nilpotentStringProjection_kernel_stable E pS d ψ hEzero y hy,rfl⟩
  · intro t x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let T := polynomialTorusOnSubmodule S hT t
    refine ⟨T y,?_,rfl⟩
    apply nilpotentStringProjection_kernel_torus_stable E T pS d ψ
      (rootScalar t a b) (integerWeightScalar v t) (by simp [rootScalar])
    · intro z
      apply Subtype.ext
      exact polynomialTorus_matrixUnit t a b z.val
    · apply Subtype.ext
      exact hv t
    · intro z
      change φ (polynomialTorus n t z.val)=_
      rw [hφT]
      have hw : integerWeightScalar (v+d • positiveRoot a b) t=
          integerWeightScalar v t * rootScalar t a b^d := by
        rw [integerWeightScalar_add]
        congr 1
        have hx (k : ℕ) : integerWeightScalar (k • positiveRoot a b) t=rootScalar t a b^k := by
          induction k with
          | zero => simp [integerWeightScalar]
          | succ k ih =>
            rw [succ_nsmul,integerWeightScalar_add,ih,integerWeightScalar_positiveRoot,pow_succ]
        exact hx d
      rw [hw]
      rfl
    · exact hy

end
end Schubert.RS.Representation
