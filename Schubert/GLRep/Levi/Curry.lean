import Schubert.GLRep.Levi.MultiplicitySpace

/-!
# Currying intertwining maps out of external tensor products

Let `L = GL_{d_0}(K) × L'` be a Levi group with first block split off, `σ_p` representations of the
blocks and `ρ` a representation of `L`. **Currying** identifies the intertwining maps
`⊠_p σ_p → ρ` with the intertwining maps of `L'` from `⊠_{q} σ_{q+1}` to the multiplicity space
`Hom_{GL_{d_0}}(σ_0, ρ)` (`GLRep.curryEquiv`): `f` corresponds to `m ↦ (x ↦ f(x ⊗ m))`.

## Main definitions

* `GLRep.consCurry`, `GLRep.consUncurry`: currying multilinear maps on `Fin (s + 1)`-families in
  their first variable, with the first variable last.
* `GLRep.tailExtTensor`: the external tensor product of the blocks after the first.
* `GLRep.curryEquiv`.
-/

namespace GLRep

open Module Representation TauCeti

noncomputable section

variable {K : Type*} [Field K]
variable {W : Type*} [AddCommGroup W] [Module K W]
variable {s : ℕ} {V : Fin (s + 1) → Type*} [∀ p, AddCommGroup (V p)] [∀ p, Module K (V p)]

/-! ### Currying multilinear maps in the first variable -/

/-- A linear map into multilinear maps, as a multilinear map into linear maps. -/
def multilinearFlip {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    {X : Type*} [AddCommGroup X] [Module K X] (L : X →ₗ[K] MultilinearMap K M W) :
    MultilinearMap K M (X →ₗ[K] W) where
  toFun m :=
    { toFun := fun x => L x m
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  map_update_add' m i a b := LinearMap.ext fun x => (L x).map_update_add m i a b
  map_update_smul' m i c a := LinearMap.ext fun x => (L x).map_update_smul m i c a

/-- A multilinear map into linear maps, as a linear map into multilinear maps. -/
def multilinearFlip' {ι : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] {X : Type*} [AddCommGroup X] [Module K X]
    (G : MultilinearMap K M (X →ₗ[K] W)) : X →ₗ[K] MultilinearMap K M W where
  toFun x := (LinearMap.applyₗ (R := K) x).compMultilinearMap G
  map_add' x y := MultilinearMap.ext fun m => map_add (G m) x y
  map_smul' c x := MultilinearMap.ext fun m => map_smul (G m) c x

/-- `m ↦ (x ↦ F (x, m))`: a multilinear map on a `Fin (s + 1)`-family as a multilinear map on the
last `s` variables with values in the linear maps on the first. -/
def consCurry (F : MultilinearMap K V W) :
    MultilinearMap K (fun q : Fin s => V q.succ) (V 0 →ₗ[K] W) :=
  multilinearFlip F.curryLeft

@[simp] theorem consCurry_apply (F : MultilinearMap K V W) (m : (q : Fin s) → V q.succ)
    (x : V 0) : consCurry F m x = F (Fin.cons x m) := rfl

/-- `m ↦ G (tail m) (m 0)`: the inverse of `GLRep.consCurry`. -/
def consUncurry (G : MultilinearMap K (fun q : Fin s => V q.succ) (V 0 →ₗ[K] W)) :
    MultilinearMap K V W :=
  (multilinearFlip' G).uncurryLeft

@[simp] theorem consUncurry_apply (G : MultilinearMap K (fun q : Fin s => V q.succ) (V 0 →ₗ[K] W))
    (m : (p : Fin (s + 1)) → V p) : consUncurry G m = G (Fin.tail m) (m 0) := rfl

/-! ### External tensor products and the first block -/

variable {d : Fin (s + 1) → ℕ} (σ : (p : Fin (s + 1)) → Representation K (GL (Fin (d p)) K) (V p))

/-- The external tensor product of the blocks after the first. -/
abbrev tailExtTensor : Representation K (LeviGroup K (Fin.tail d))
    (PiTensorProduct K fun q : Fin s => V q.succ) :=
  extTensor (d := Fin.tail d) (V' := fun q => V q.succ) fun q => σ q.succ

theorem tailExtTensor_tprod (h : LeviGroup K (Fin.tail d)) (m : (q : Fin s) → V q.succ) :
    tailExtTensor σ h (PiTensorProduct.tprod K m) =
      PiTensorProduct.tprod K fun q : Fin s => σ q.succ (h q) (m q) :=
  extTensor_tprod _ _ _

theorem extTensor_leviBlock_tprod_cons (g : GL (Fin (d 0)) K) (x : V 0)
    (m : (q : Fin s) → V q.succ) :
    extTensor σ (leviBlock K d 0 g) (PiTensorProduct.tprod K (Fin.cons x m)) =
      PiTensorProduct.tprod K (Fin.cons (σ 0 g x) m) := by
  rw [extTensor_tprod]
  congr 1
  funext p
  induction p using Fin.cases with
  | zero => rw [leviBlock_zero_apply_zero, Fin.cons_zero, Fin.cons_zero]
  | succ q =>
    rw [leviBlock_zero_apply_succ, map_one, Module.End.one_apply]
    simp only [Fin.cons_succ]

theorem extTensor_leviTail_tprod_cons (h : LeviGroup K (Fin.tail d)) (x : V 0)
    (m : (q : Fin s) → V q.succ) :
    extTensor σ (leviTail K d h) (PiTensorProduct.tprod K (Fin.cons x m)) =
      PiTensorProduct.tprod K (Fin.cons x fun q => σ q.succ (h q) (m q)) := by
  rw [extTensor_tprod]
  congr 1
  funext p
  induction p using Fin.cases with
  | zero =>
    rw [leviTail_apply_zero, map_one, Module.End.one_apply]
    simp only [Fin.cons_zero]
  | succ q => rfl

/-! ### Currying intertwining maps -/

variable {ρ : Representation K (LeviGroup K d) W}

variable {σ} in
/-- The multilinear map `m ↦ (x ↦ f(x ⊗ m))` with values in the multiplicity space. -/
def curryMultilinear (f : IntertwiningMap (extTensor σ) ρ) :
    MultilinearMap K (fun q : Fin s => V q.succ) (IntertwiningMap (σ 0) (headRep ρ)) where
  toFun m := ⟨consCurry (f.toLinearMap.compMultilinearMap (PiTensorProduct.tprod K)) m,
    fun g => LinearMap.ext fun x => by
      change f (PiTensorProduct.tprod K (Fin.cons (σ 0 g x) m)) =
        ρ (leviBlock K d 0 g) (f (PiTensorProduct.tprod K (Fin.cons x m)))
      rw [← extTensor_leviBlock_tprod_cons, f.isIntertwining]⟩
  map_update_add' m i a b := IntertwiningMap.ext
    ((consCurry (f.toLinearMap.compMultilinearMap (PiTensorProduct.tprod K))).map_update_add
      m i a b)
  map_update_smul' m i c a := IntertwiningMap.ext
    ((consCurry (f.toLinearMap.compMultilinearMap (PiTensorProduct.tprod K))).map_update_smul
      m i c a)

variable {σ} in
/-- Currying an intertwining map out of an external tensor product. -/
def curryIntertwining (f : IntertwiningMap (extTensor σ) ρ) :
    IntertwiningMap (tailExtTensor σ) (multRep ρ (σ 0)) where
  toLinearMap := PiTensorProduct.lift (curryMultilinear f)
  isIntertwining' h := PiTensorProduct.ext (MultilinearMap.ext fun m =>
    IntertwiningMap.ext (LinearMap.ext fun x => by
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
      rw [tailExtTensor_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
      change f (PiTensorProduct.tprod K (Fin.cons x fun q => σ q.succ (h q) (m q))) =
        ρ (leviTail K d h) (f (PiTensorProduct.tprod K (Fin.cons x m)))
      rw [← extTensor_leviTail_tprod_cons, f.isIntertwining]))

theorem curryIntertwining_tprod (f : IntertwiningMap (extTensor σ) ρ)
    (m : (q : Fin s) → V q.succ) (x : V 0) :
    curryIntertwining f (PiTensorProduct.tprod K m) x =
      f (PiTensorProduct.tprod K (Fin.cons x m)) := by
  change PiTensorProduct.lift (curryMultilinear f) (PiTensorProduct.tprod K m) x = _
  rw [PiTensorProduct.lift.tprod]
  rfl

variable {σ} in
/-- The inverse of currying. -/
def uncurryIntertwining (F : IntertwiningMap (tailExtTensor σ) (multRep ρ (σ 0))) :
    IntertwiningMap (extTensor σ) ρ where
  toLinearMap := PiTensorProduct.lift (consUncurry
    (((intertwiningMapToLinearMap (σ 0) (headRep ρ)) ∘ₗ F.toLinearMap).compMultilinearMap
      (PiTensorProduct.tprod K)))
  isIntertwining' g := PiTensorProduct.ext (MultilinearMap.ext fun m => by
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      PiTensorProduct.lift.tprod, consUncurry_apply]
    rw [extTensor_tprod, PiTensorProduct.lift.tprod, consUncurry_apply]
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply]
    set g' : LeviGroup K (Fin.tail d) := Fin.tail g with hg'
    have key : F (PiTensorProduct.tprod K fun q => σ q.succ (g' q) (Fin.tail m q)) =
        multRep ρ (σ 0) g' (F (PiTensorProduct.tprod K (Fin.tail m))) := by
      rw [← tailExtTensor_tprod, F.isIntertwining]
    change F (PiTensorProduct.tprod K fun q => σ q.succ (g' q) (Fin.tail m q))
        (σ 0 (g 0) (m 0)) = ρ g (F (PiTensorProduct.tprod K (Fin.tail m)) (m 0))
    rw [key]
    change tailRep ρ g' (F (PiTensorProduct.tprod K (Fin.tail m)) (σ 0 (g 0) (m 0))) =
      ρ g (F (PiTensorProduct.tprod K (Fin.tail m)) (m 0))
    rw [(F (PiTensorProduct.tprod K (Fin.tail m))).isIntertwining]
    change ρ (leviTail K d g') (ρ (leviBlock K d 0 (g 0)) _) = _
    rw [← Module.End.mul_apply, ← map_mul, ← (leviBlock_commute_leviTail (g 0) g').eq, hg',
      leviBlock_mul_leviTail])

theorem uncurryIntertwining_tprod (F : IntertwiningMap (tailExtTensor σ) (multRep ρ (σ 0)))
    (m : (p : Fin (s + 1)) → V p) :
    uncurryIntertwining F (PiTensorProduct.tprod K m) =
      F (PiTensorProduct.tprod K (Fin.tail m)) (m 0) := by
  change PiTensorProduct.lift _ (PiTensorProduct.tprod K m) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

/-- **Currying**: `Hom_L(⊠_p σ_p, ρ) ≃ Hom_{L'}(⊠_q σ_{q+1}, Hom_{GL_{d_0}}(σ_0, ρ))`. -/
def curryEquiv :
    IntertwiningMap (extTensor σ) ρ ≃ₗ[K] IntertwiningMap (tailExtTensor σ) (multRep ρ (σ 0)) where
  toFun := curryIntertwining
  invFun := uncurryIntertwining
  map_add' f g := IntertwiningMap.ext (PiTensorProduct.ext (MultilinearMap.ext fun m =>
    IntertwiningMap.ext (LinearMap.ext fun x => by
      simp only [LinearMap.compMultilinearMap_apply]
      change curryIntertwining (f + g) _ x = curryIntertwining f _ x + curryIntertwining g _ x
      rw [curryIntertwining_tprod, curryIntertwining_tprod, curryIntertwining_tprod]
      rfl)))
  map_smul' c f := IntertwiningMap.ext (PiTensorProduct.ext (MultilinearMap.ext fun m =>
    IntertwiningMap.ext (LinearMap.ext fun x => by
      simp only [LinearMap.compMultilinearMap_apply]
      change curryIntertwining (c • f) _ x = c • curryIntertwining f _ x
      rw [curryIntertwining_tprod, curryIntertwining_tprod]
      rfl)))
  left_inv f := IntertwiningMap.ext (PiTensorProduct.ext (MultilinearMap.ext fun m => by
    simp only [LinearMap.compMultilinearMap_apply]
    change uncurryIntertwining (curryIntertwining f) _ = f _
    rw [uncurryIntertwining_tprod, curryIntertwining_tprod, Fin.cons_self_tail]))
  right_inv F := IntertwiningMap.ext (PiTensorProduct.ext (MultilinearMap.ext fun m =>
    IntertwiningMap.ext (LinearMap.ext fun x => by
      simp only [LinearMap.compMultilinearMap_apply]
      change curryIntertwining (uncurryIntertwining F) _ x = F _ x
      rw [curryIntertwining_tprod, uncurryIntertwining_tprod, Fin.tail_cons, Fin.cons_zero])))

end

end GLRep
