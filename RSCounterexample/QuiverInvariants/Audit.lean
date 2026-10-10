import RSCounterexample.QuiverInvariants.Main

/-!
# Audit of the library

Prints the main results of the library indexed in `RSCounterexample/QuiverInvariants/Main.lean`, with
the axioms they depend on. Each `#print axioms` below should report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- Generic points
#check @QuiverInvariants.ZariskiDense.exists_of_eventually
#check @QuiverInvariants.ZariskiDense.image
#check @QuiverInvariants.ZariskiDense.sumElim
#check @QuiverInvariants.ZariskiDense.preimage_comp
#check @QuiverInvariants.eventually_exists_left
#check @QuiverInvariants.le_rank_iff_exists_det_submatrix_ne_zero
#check @QuiverInvariants.exists_minor_genericRank
#check @QuiverInvariants.eventually_rank_eq_genericRank
#print axioms QuiverInvariants.ZariskiDense.exists_of_eventually
#print axioms QuiverInvariants.ZariskiDense.image
#print axioms QuiverInvariants.ZariskiDense.sumElim
#print axioms QuiverInvariants.ZariskiDense.preimage_comp
#print axioms QuiverInvariants.eventually_exists_left
#print axioms QuiverInvariants.le_rank_iff_exists_det_submatrix_ne_zero
#print axioms QuiverInvariants.exists_minor_genericRank
#print axioms QuiverInvariants.eventually_rank_eq_genericRank

-- Representations, `hom` and `ext`
#check @QuiverInvariants.FQuiver.homDim_sub_extDim
#check @QuiverInvariants.FQuiver.genericHom_sub_genericExt
#check @QuiverInvariants.FQuiver.eventually_isHomGeneric
#check @QuiverInvariants.FQuiver.IsHomGeneric.hom_mul_mem_range
#check @QuiverInvariants.FQuiver.IsHomGeneric.extDim_blockRep_eq
#print axioms QuiverInvariants.FQuiver.homDim_sub_extDim
#print axioms QuiverInvariants.FQuiver.genericHom_sub_genericExt
#print axioms QuiverInvariants.FQuiver.eventually_isHomGeneric
#print axioms QuiverInvariants.FQuiver.IsHomGeneric.hom_mul_mem_range
#print axioms QuiverInvariants.FQuiver.IsHomGeneric.extDim_blockRep_eq

-- Schofield's formula
#check @QuiverInvariants.FQuiver.exists_normalForm
#check @QuiverInvariants.FQuiver.GeneralQuot.of_generalSub
#check @QuiverInvariants.FQuiver.exists_cokernelStep
#check @QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos
#check @QuiverInvariants.FQuiver.exists_extDim_eq_zero
#check @QuiverInvariants.FQuiver.isGreatest_genericExt
#print axioms QuiverInvariants.FQuiver.exists_normalForm
#print axioms QuiverInvariants.FQuiver.GeneralQuot.of_generalSub
#print axioms QuiverInvariants.FQuiver.exists_cokernelStep
#print axioms QuiverInvariants.FQuiver.exists_generalQuot_euler_add_extDim_nonpos
#print axioms QuiverInvariants.FQuiver.exists_extDim_eq_zero
#print axioms QuiverInvariants.FQuiver.isGreatest_genericExt

-- King's inequalities
#check @QuiverInvariants.FQuiver.act_oneParam
#check @QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_finrank_nonpos
#check @QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_card_eq_zero
#check @QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot
#print axioms QuiverInvariants.FQuiver.act_oneParam
#print axioms QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_finrank_nonpos
#print axioms QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_card_eq_zero
#print axioms QuiverInvariants.FQuiver.IsSemiInvariant.sum_mul_nonneg_of_generalQuot

-- Positivity
#check @QuiverInvariants.liftWeight_nonneg
#check @QuiverInvariants.FQuiver.generalQuot_genericQuotDim
#check @QuiverInvariants.FQuiver.liftWeight_nonneg_of_generalQuot
#print axioms QuiverInvariants.liftWeight_nonneg
#print axioms QuiverInvariants.FQuiver.generalQuot_genericQuotDim
#print axioms QuiverInvariants.FQuiver.liftWeight_nonneg_of_generalQuot

-- Determinantal semi-invariants
#check @QuiverInvariants.det_pi_of_family
#check @QuiverInvariants.FQuiver.isSemiInvariant_detSemiInvariant
#check @QuiverInvariants.FQuiver.detSemiInvariant_ne_zero
#check @QuiverInvariants.FQuiver.exists_semiInvariant_of_extDim_eq_zero
#print axioms QuiverInvariants.det_pi_of_family
#print axioms QuiverInvariants.FQuiver.isSemiInvariant_detSemiInvariant
#print axioms QuiverInvariants.FQuiver.detSemiInvariant_ne_zero
#print axioms QuiverInvariants.FQuiver.exists_semiInvariant_of_extDim_eq_zero

-- Semi-invariants and saturation
#check @QuiverInvariants.FQuiver.exists_semiInvariant_iff
#check @QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul
#print axioms QuiverInvariants.FQuiver.exists_semiInvariant_iff
#print axioms QuiverInvariants.FQuiver.exists_semiInvariant_of_nsmul
