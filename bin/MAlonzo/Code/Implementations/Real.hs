{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Implementations.Real where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Real
import qualified MAlonzo.Code.Relation.Binary.Structures

-- _.IsAbelianGroup
d_IsAbelianGroup_6 a0 a1 a2 = ()
-- _.IsAlternativeMagma
d_IsAlternativeMagma_8 a0 = ()
-- _.IsBand
d_IsBand_10 a0 = ()
-- _.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_12 a0 a1 a2 a3 = ()
-- _.IsCommutativeMagma
d_IsCommutativeMagma_14 a0 = ()
-- _.IsCommutativeMonoid
d_IsCommutativeMonoid_16 a0 a1 = ()
-- _.IsCommutativeRing
d_IsCommutativeRing_18 a0 a1 a2 a3 a4 = ()
-- _.IsCommutativeSemigroup
d_IsCommutativeSemigroup_20 a0 = ()
-- _.IsCommutativeSemiring
d_IsCommutativeSemiring_22 a0 a1 a2 a3 = ()
-- _.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_24 a0 a1 a2 = ()
-- _.IsFlexibleMagma
d_IsFlexibleMagma_26 a0 = ()
-- _.IsGroup
d_IsGroup_28 a0 a1 a2 = ()
-- _.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_30 a0 a1 = ()
-- _.IsIdempotentMagma
d_IsIdempotentMagma_32 a0 = ()
-- _.IsIdempotentSemiring
d_IsIdempotentSemiring_34 a0 a1 a2 a3 = ()
-- _.IsInvertibleMagma
d_IsInvertibleMagma_36 a0 a1 a2 = ()
-- _.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_38 a0 a1 a2 = ()
-- _.IsKleeneAlgebra
d_IsKleeneAlgebra_40 a0 a1 a2 a3 a4 = ()
-- _.IsLeftBolLoop
d_IsLeftBolLoop_42 a0 a1 a2 a3 = ()
-- _.IsLoop
d_IsLoop_44 a0 a1 a2 a3 = ()
-- _.IsMagma
d_IsMagma_46 a0 = ()
-- _.IsMedialMagma
d_IsMedialMagma_48 a0 = ()
-- _.IsMiddleBolLoop
d_IsMiddleBolLoop_50 a0 a1 a2 a3 = ()
-- _.IsMonoid
d_IsMonoid_52 a0 a1 = ()
-- _.IsMoufangLoop
d_IsMoufangLoop_54 a0 a1 a2 a3 = ()
-- _.IsNearSemiring
d_IsNearSemiring_56 a0 a1 a2 = ()
-- _.IsNearring
d_IsNearring_58 a0 a1 a2 a3 a4 = ()
-- _.IsNonAssociativeRing
d_IsNonAssociativeRing_60 a0 a1 a2 a3 a4 = ()
-- _.IsQuasigroup
d_IsQuasigroup_62 a0 a1 a2 = ()
-- _.IsQuasiring
d_IsQuasiring_64 a0 a1 a2 a3 = ()
-- _.IsRightBolLoop
d_IsRightBolLoop_66 a0 a1 a2 a3 = ()
-- _.IsRing
d_IsRing_68 a0 a1 a2 a3 a4 = ()
-- _.IsRingWithoutOne
d_IsRingWithoutOne_70 a0 a1 a2 a3 = ()
-- _.IsSelectiveMagma
d_IsSelectiveMagma_72 a0 = ()
-- _.IsSemigroup
d_IsSemigroup_74 a0 = ()
-- _.IsSemimedialMagma
d_IsSemimedialMagma_76 a0 = ()
-- _.IsSemiring
d_IsSemiring_78 a0 a1 a2 a3 = ()
-- _.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_80 a0 a1 a2 a3 = ()
-- _.IsSemiringWithoutOne
d_IsSemiringWithoutOne_82 a0 a1 a2 = ()
-- _.IsUnitalMagma
d_IsUnitalMagma_84 a0 a1 = ()
-- _.IsAbelianGroup.assoc
d_assoc_90 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_90 = erased
-- _.IsAbelianGroup.comm
d_comm_92 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_92 = erased
-- _.IsAbelianGroup.identity
d_identity_94 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_94 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_992 (coe v0)))
-- _.IsAbelianGroup.inverse
d_inverse_100 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_100 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_908
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_992 (coe v0))
-- _.IsAbelianGroup.isEquivalence
d_isEquivalence_112 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_112 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_906
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_992 (coe v0)))))
-- _.IsAbelianGroup.isGroup
d_isGroup_114 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892
d_isGroup_114 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_992 (coe v0)
-- _.IsAbelianGroup.isMagma
d_isMagma_120 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_120 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_906
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_992 (coe v0))))
-- _.IsAbelianGroup.isMonoid
d_isMonoid_122 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_122 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_906
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_992 (coe v0))
-- _.IsAbelianGroup.isSemigroup
d_isSemigroup_126 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_126 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_992 (coe v0)))
-- _.IsAbelianGroup.⁻¹-cong
d_'8315''185''45'cong_144 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_144 = erased
-- _.IsAbelianGroup.∙-cong
d_'8729''45'cong_146 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_146 = erased
-- _.IsAlternativeMagma.alter
d_alter_154 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_252 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_154 v0
  = coe MAlonzo.Code.Algebra.Structures.d_alter_262 (coe v0)
-- _.IsAlternativeMagma.isEquivalence
d_isEquivalence_160 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_252 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_160 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0))
-- _.IsAlternativeMagma.isMagma
d_isMagma_162 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_252 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_162 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_260 (coe v0)
-- _.IsAlternativeMagma.∙-cong
d_'8729''45'cong_176 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_252 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_176 = erased
-- _.IsBand.assoc
d_assoc_184 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_476 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_184 = erased
-- _.IsBand.idem
d_idem_186 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_476 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_186 = erased
-- _.IsBand.isEquivalence
d_isEquivalence_188 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_476 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_188 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_484 (coe v0)))
-- _.IsBand.isMagma
d_isMagma_190 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_476 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_190 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_484 (coe v0))
-- _.IsBand.isSemigroup
d_isSemigroup_194 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_476 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_194 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_484 (coe v0)
-- _.IsBand.∙-cong
d_'8729''45'cong_206 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_476 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_206 = erased
-- _.IsCancellativeCommutativeSemiring.*-assoc
d_'42''45'assoc_214 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_214 = erased
-- _.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_216 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45'nonZero_216 = erased
-- _.IsCancellativeCommutativeSemiring.*-comm
d_'42''45'comm_218 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_218 = erased
-- _.IsCancellativeCommutativeSemiring.*-cong
d_'42''45'cong_220 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_220 = erased
-- _.IsCancellativeCommutativeSemiring.*-identity
d_'42''45'identity_226 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_226 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1342
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
               (coe v0))))
-- _.IsCancellativeCommutativeSemiring.assoc
d_assoc_244 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_244 = erased
-- _.IsCancellativeCommutativeSemiring.comm
d_comm_246 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_246 = erased
-- _.IsCancellativeCommutativeSemiring.∙-cong
d_'8729''45'cong_248 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_248 = erased
-- _.IsCancellativeCommutativeSemiring.identity
d_identity_254 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_254 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
                     (coe v0))))))
-- _.IsCancellativeCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_262 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_'43''45'isCommutativeMonoid_262 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
               (coe v0))))
-- _.IsCancellativeCommutativeSemiring.isMagma
d_isMagma_266 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_664
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
                        (coe v0)))))))
-- _.IsCancellativeCommutativeSemiring.isMonoid
d_isMonoid_268 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_268 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
                  (coe v0)))))
-- _.IsCancellativeCommutativeSemiring.isSemigroup
d_isSemigroup_270 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
                     (coe v0))))))
-- _.IsCancellativeCommutativeSemiring.distrib
d_distrib_274 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_274 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1344
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
               (coe v0))))
-- _.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_280 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526
d_isCommutativeSemiring_280 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
      (coe v0)
-- _.IsCancellativeCommutativeSemiring.isEquivalence
d_isEquivalence_284 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_284 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_664
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
                           (coe v0))))))))
-- _.IsCancellativeCommutativeSemiring.isSemiring
d_isSemiring_290 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418
d_isSemiring_290 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
         (coe v0))
-- _.IsCancellativeCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_292 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316
d_isSemiringWithoutAnnihilatingZero_292 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
            (coe v0)))
-- _.IsCancellativeCommutativeSemiring.zero
d_zero_306 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1646 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_306 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1434
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1540
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1660
            (coe v0)))
-- _.IsCommutativeMagma.comm
d_comm_314 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_180 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_314 = erased
-- _.IsCommutativeMagma.isEquivalence
d_isEquivalence_316 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_316 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_188 (coe v0))
-- _.IsCommutativeMagma.isMagma
d_isMagma_318 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_180 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_318 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_188 (coe v0)
-- _.IsCommutativeMagma.∙-cong
d_'8729''45'cong_332 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_180 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_332 = erased
-- _.IsCommutativeMonoid.assoc
d_assoc_340 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_340 = erased
-- _.IsCommutativeMonoid.comm
d_comm_342 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_342 = erased
-- _.IsCommutativeMonoid.identity
d_identity_344 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_344 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_664 (coe v0))
-- _.IsCommutativeMonoid.isEquivalence
d_isEquivalence_354 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_354 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_664 (coe v0))))
-- _.IsCommutativeMonoid.isMagma
d_isMagma_356 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_356 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_664 (coe v0)))
-- _.IsCommutativeMonoid.isMonoid
d_isMonoid_358 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_358 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_664 (coe v0)
-- _.IsCommutativeMonoid.isSemigroup
d_isSemigroup_362 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_362 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_664 (coe v0))
-- _.IsCommutativeMonoid.∙-cong
d_'8729''45'cong_376 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_376 = erased
-- _.IsCommutativeRing.*-assoc
d_'42''45'assoc_386 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_386 = erased
-- _.IsCommutativeRing.*-comm
d_'42''45'comm_388 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_388 = erased
-- _.IsCommutativeRing.*-cong
d_'42''45'cong_390 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_390 = erased
-- _.IsCommutativeRing.*-identity
d_'42''45'identity_396 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_396 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2506
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0))
-- _.IsCommutativeRing.assoc
d_assoc_414 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_414 = erased
-- _.IsCommutativeRing.comm
d_comm_416 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_416 = erased
-- _.IsCommutativeRing.∙-cong
d_'8729''45'cong_418 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_418 = erased
-- _.IsCommutativeRing.identity
d_identity_424 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_424 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_424 v5
du_identity_424 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_424 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_616
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_906
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_992
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
                  (coe v1)))))
-- _.IsCommutativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_430 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980
d_'43''45'isAbelianGroup_430 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0))
-- _.IsCommutativeRing.isGroup
d_isGroup_438 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892
d_isGroup_438 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_438 v5
du_isGroup_438 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892
du_isGroup_438 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_992
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
            (coe v1)))
-- _.IsCommutativeRing.isMagma
d_isMagma_444 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_444 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_444 v5
du_isMagma_444 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
du_isMagma_444 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_906
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_992
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
                     (coe v1))))))
-- _.IsCommutativeRing.isMonoid
d_isMonoid_446 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_446 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_446 v5
du_isMonoid_446 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
du_isMonoid_446 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_992
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
               (coe v1))))
-- _.IsCommutativeRing.isSemigroup
d_isSemigroup_448 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_448 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_448 v5
du_isSemigroup_448 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
du_isSemigroup_448 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_906
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_992
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
                  (coe v1)))))
-- _.IsCommutativeRing.⁻¹-cong
d_'8315''185''45'cong_452 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_452 = erased
-- _.IsCommutativeRing.inverse
d_inverse_454 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_454 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_454 v5
du_inverse_454 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_454 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_inverse_908
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_992
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
               (coe v1))))
-- _.IsCommutativeRing.distrib
d_distrib_460 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_460 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2508
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0))
-- _.IsCommutativeRing.isEquivalence
d_isEquivalence_470 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_470 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_470 v5
du_isEquivalence_470 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_470 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_448
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_906
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_992
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
                        (coe v1)))))))
-- _.IsCommutativeRing.isRing
d_isRing_476 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478
d_isRing_476 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0)
-- _.IsCommutativeRing.isRingWithoutOne
d_isRingWithoutOne_478 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114
d_isRingWithoutOne_478 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isRingWithoutOne_478 v5
du_isRingWithoutOne_478 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114
du_isRingWithoutOne_478 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2510
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2640 (coe v0))
-- _.IsCommutativeSemigroup.assoc
d_assoc_508 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_516 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_508 = erased
-- _.IsCommutativeSemigroup.comm
d_comm_510 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_516 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_510 = erased
-- _.IsCommutativeSemigroup.isEquivalence
d_isEquivalence_514 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_516 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_514 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_524 (coe v0)))
-- _.IsCommutativeSemigroup.isMagma
d_isMagma_516 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_516 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_516 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_524 (coe v0))
-- _.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_520 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_516 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_520 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_524 (coe v0)
-- _.IsCommutativeSemigroup.∙-cong
d_'8729''45'cong_532 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_516 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_532 = erased
-- _.IsCommutativeSemiring.*-assoc
d_'42''45'assoc_540 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_540 = erased
-- _.IsCommutativeSemiring.*-comm
d_'42''45'comm_542 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_542 = erased
-- _.IsCommutativeSemiring.*-cong
d_'42''45'cong_544 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_544 = erased
-- _.IsCommutativeSemiring.*-identity
d_'42''45'identity_550 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_550 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1342
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0)))
-- _.IsCommutativeSemiring.assoc
d_assoc_568 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_568 = erased
-- _.IsCommutativeSemiring.comm
d_comm_570 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_570 = erased
-- _.IsCommutativeSemiring.∙-cong
d_'8729''45'cong_572 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_572 = erased
-- _.IsCommutativeSemiring.identity
d_identity_578 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_578 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0)))))
-- _.IsCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_586 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_'43''45'isCommutativeMonoid_586 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0)))
-- _.IsCommutativeSemiring.isMagma
d_isMagma_590 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_590 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_664
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0))))))
-- _.IsCommutativeSemiring.isMonoid
d_isMonoid_592 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_592 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0))))
-- _.IsCommutativeSemiring.isSemigroup
d_isSemigroup_594 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_594 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0)))))
-- _.IsCommutativeSemiring.distrib
d_distrib_598 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_598 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1344
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0)))
-- _.IsCommutativeSemiring.isEquivalence
d_isEquivalence_606 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_606 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_664
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0)))))))
-- _.IsCommutativeSemiring.isSemiring
d_isSemiring_612 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418
d_isSemiring_612 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0)
-- _.IsCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_614 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316
d_isSemiringWithoutAnnihilatingZero_614 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0))
-- _.IsCommutativeSemiring.zero
d_zero_628 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1526 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_628 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1434
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1540 (coe v0))
-- _.IsCommutativeSemiringWithoutOne.*-assoc
d_'42''45'assoc_640 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_640 = erased
-- _.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_642 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_642 = erased
-- _.IsCommutativeSemiringWithoutOne.*-cong
d_'42''45'cong_644 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_644 = erased
-- _.IsCommutativeSemiringWithoutOne.comm
d_comm_658 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_658 = erased
-- _.IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_662 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_'43''45'isCommutativeMonoid_662 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1164
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1242
         (coe v0))
-- _.IsCommutativeSemiringWithoutOne.isMonoid
d_isMonoid_666 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_666 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1164
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1242
            (coe v0)))
-- _.IsCommutativeSemiringWithoutOne.distrib
d_distrib_670 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_670 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1170
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1242
         (coe v0))
-- _.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_678 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1146
d_isSemiringWithoutOne_678 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1242
      (coe v0)
-- _.IsCommutativeSemiringWithoutOne.zero
d_zero_692 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1230 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_692 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1172
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1242
         (coe v0))
-- _.IsFlexibleMagma.flex
d_flex_700 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_292 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flex_700 = erased
-- _.IsFlexibleMagma.isEquivalence
d_isEquivalence_702 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_292 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_702 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_300 (coe v0))
-- _.IsFlexibleMagma.isMagma
d_isMagma_704 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_292 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_704 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_300 (coe v0)
-- _.IsFlexibleMagma.∙-cong
d_'8729''45'cong_718 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_292 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_718 = erased
-- _.IsGroup.assoc
d_assoc_728 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_728 = erased
-- _.IsGroup.identity
d_identity_730 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_730 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_906 (coe v0))
-- _.IsGroup.inverse
d_inverse_736 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_736 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_908 (coe v0)
-- _.IsGroup.isEquivalence
d_isEquivalence_742 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_742 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_906 (coe v0))))
-- _.IsGroup.isMagma
d_isMagma_748 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_748 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_906 (coe v0)))
-- _.IsGroup.isMonoid
d_isMonoid_750 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_750 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_906 (coe v0)
-- _.IsGroup.isSemigroup
d_isSemigroup_754 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_754 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_906 (coe v0))
-- _.IsGroup.⁻¹-cong
d_'8315''185''45'cong_772 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_772 = erased
-- _.IsGroup.∙-cong
d_'8729''45'cong_774 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_774 = erased
-- _.IsIdempotentCommutativeMonoid.assoc
d_assoc_782 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_782 = erased
-- _.IsIdempotentCommutativeMonoid.comm
d_comm_784 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_784 = erased
-- _.IsIdempotentCommutativeMonoid.idem
d_idem_786 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_786 = erased
-- _.IsIdempotentCommutativeMonoid.identity
d_identity_788 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_788 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_724
            (coe v0)))
-- _.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_798 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_isCommutativeMonoid_798 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_724 (coe v0)
-- _.IsIdempotentCommutativeMonoid.isEquivalence
d_isEquivalence_802 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_802 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_664
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_724
                  (coe v0)))))
-- _.IsIdempotentCommutativeMonoid.isMagma
d_isMagma_804 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_804 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_664
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_724
               (coe v0))))
-- _.IsIdempotentCommutativeMonoid.isMonoid
d_isMonoid_806 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_806 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_724 (coe v0))
-- _.IsIdempotentCommutativeMonoid.isSemigroup
d_isSemigroup_810 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_810 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_724
            (coe v0)))
-- _.IsIdempotentCommutativeMonoid.∙-cong
d_'8729''45'cong_824 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_714 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_824 = erased
-- _.IsIdempotentMagma.idem
d_idem_832 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_216 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_832 = erased
-- _.IsIdempotentMagma.isEquivalence
d_isEquivalence_834 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_216 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_834 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_224 (coe v0))
-- _.IsIdempotentMagma.isMagma
d_isMagma_836 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_216 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_836 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_224 (coe v0)
-- _.IsIdempotentMagma.∙-cong
d_'8729''45'cong_850 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_216 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_850 = erased
-- _.IsIdempotentSemiring.*-assoc
d_'42''45'assoc_858 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_858 = erased
-- _.IsIdempotentSemiring.*-cong
d_'42''45'cong_860 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_860 = erased
-- _.IsIdempotentSemiring.*-identity
d_'42''45'identity_866 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_866 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1342
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0)))
-- _.IsIdempotentSemiring.assoc
d_assoc_878 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_878 = erased
-- _.IsIdempotentSemiring.comm
d_comm_880 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_880 = erased
-- _.IsIdempotentSemiring.∙-cong
d_'8729''45'cong_882 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_882 = erased
-- _.IsIdempotentSemiring.+-idem
d_'43''45'idem_888 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_888 = erased
-- _.IsIdempotentSemiring.identity
d_identity_890 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_890 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0)))))
-- _.IsIdempotentSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_898 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_'43''45'isCommutativeMonoid_898 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0)))
-- _.IsIdempotentSemiring.isMagma
d_isMagma_902 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_902 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_664
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0))))))
-- _.IsIdempotentSemiring.isMonoid
d_isMonoid_904 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_904 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0))))
-- _.IsIdempotentSemiring.isSemigroup
d_isSemigroup_906 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_906 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0)))))
-- _.IsIdempotentSemiring.distrib
d_distrib_910 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_910 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1344
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0)))
-- _.IsIdempotentSemiring.isEquivalence
d_isEquivalence_916 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_916 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_664
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0)))))))
-- _.IsIdempotentSemiring.isSemiring
d_isSemiring_922 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418
d_isSemiring_922 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0)
-- _.IsIdempotentSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_924 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316
d_isSemiringWithoutAnnihilatingZero_924 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0))
-- _.IsIdempotentSemiring.zero
d_zero_938 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_938 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1434
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1782 (coe v0))
-- _.IsInvertibleMagma.inverse
d_inverse_946 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_780 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_946 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_796 (coe v0)
-- _.IsInvertibleMagma.isEquivalence
d_isEquivalence_952 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_780 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_952 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_794 (coe v0))
-- _.IsInvertibleMagma.isMagma
d_isMagma_954 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_780 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_954 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_794 (coe v0)
-- _.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_968 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_780 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_968 = erased
-- _.IsInvertibleMagma.∙-cong
d_'8729''45'cong_970 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_780 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_970 = erased
-- _.IsInvertibleUnitalMagma.identity
d_identity_978 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_832 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_978 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_846 (coe v0)
-- _.IsInvertibleUnitalMagma.inverse
d_inverse_984 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_832 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_984 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_796
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_844 (coe v0))
-- _.IsInvertibleUnitalMagma.isEquivalence
d_isEquivalence_990 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_832 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_990 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_794
         (coe
            MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_844 (coe v0)))
-- _.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_992 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_832 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_780
d_isInvertibleMagma_992 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_844 (coe v0)
-- _.IsInvertibleUnitalMagma.isMagma
d_isMagma_994 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_832 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_994 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_794
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_844 (coe v0))
-- _.IsInvertibleUnitalMagma.⁻¹-cong
d_'8315''185''45'cong_1010 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_832 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1010 = erased
-- _.IsInvertibleUnitalMagma.∙-cong
d_'8729''45'cong_1012 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_832 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1012 = erased
-- _.IsKleeneAlgebra.*-assoc
d_'42''45'assoc_1020 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1020 = erased
-- _.IsKleeneAlgebra.*-cong
d_'42''45'cong_1022 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1022 = erased
-- _.IsKleeneAlgebra.*-identity
d_'42''45'identity_1028 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1028 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1342
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
               (coe v0))))
-- _.IsKleeneAlgebra.assoc
d_assoc_1040 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1040 = erased
-- _.IsKleeneAlgebra.comm
d_comm_1042 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1042 = erased
-- _.IsKleeneAlgebra.∙-cong
d_'8729''45'cong_1044 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1044 = erased
-- _.IsKleeneAlgebra.+-idem
d_'43''45'idem_1050 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1050 = erased
-- _.IsKleeneAlgebra.identity
d_identity_1052 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1052 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
                     (coe v0))))))
-- _.IsKleeneAlgebra.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1060 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_'43''45'isCommutativeMonoid_1060 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
               (coe v0))))
-- _.IsKleeneAlgebra.isMagma
d_isMagma_1064 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1064 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_664
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
                        (coe v0)))))))
-- _.IsKleeneAlgebra.isMonoid
d_isMonoid_1066 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_1066 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
                  (coe v0)))))
-- _.IsKleeneAlgebra.isSemigroup
d_isSemigroup_1068 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_1068 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
                     (coe v0))))))
-- _.IsKleeneAlgebra.distrib
d_distrib_1072 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1072 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1344
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
               (coe v0))))
-- _.IsKleeneAlgebra.isEquivalence
d_isEquivalence_1078 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1078 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_664
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
                           (coe v0))))))))
-- _.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_1080 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1768
d_isIdempotentSemiring_1080 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
      (coe v0)
-- _.IsKleeneAlgebra.isSemiring
d_isSemiring_1086 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418
d_isSemiring_1086 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
         (coe v0))
-- _.IsKleeneAlgebra.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1088 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316
d_isSemiringWithoutAnnihilatingZero_1088 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
            (coe v0)))
-- _.IsKleeneAlgebra.starDestructive
d_starDestructive_1098 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_1098 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_starDestructive_1902 (coe v0)
-- _.IsKleeneAlgebra.starExpansive
d_starExpansive_1104 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_1104 v0
  = coe MAlonzo.Code.Algebra.Structures.d_starExpansive_1900 (coe v0)
-- _.IsKleeneAlgebra.zero
d_zero_1114 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_1880 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1114 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1434
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1782
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_1898
            (coe v0)))
-- _.IsLeftBolLoop.//-cong
d_'47''47''45'cong_1122 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1122 = erased
-- _.IsLeftBolLoop.\\-cong
d_'92''92''45'cong_1128 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1128 = erased
-- _.IsLeftBolLoop.identity
d_identity_1134 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1134 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_2870
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_2946 (coe v0))
-- _.IsLeftBolLoop.isEquivalence
d_isEquivalence_1140 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1140 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2790
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_2946 (coe v0))))
-- _.IsLeftBolLoop.isLoop
d_isLoop_1142 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854
d_isLoop_1142 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_2946 (coe v0)
-- _.IsLeftBolLoop.isMagma
d_isMagma_1144 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1144 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2790
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_2946 (coe v0)))
-- _.IsLeftBolLoop.isQuasigroup
d_isQuasigroup_1148 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772
d_isQuasigroup_1148 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_2946 (coe v0))
-- _.IsLeftBolLoop.leftBol
d_leftBol_1150 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1150 = erased
-- _.IsLeftBolLoop.leftDivides
d_leftDivides_1152 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1152 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2796
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_2946 (coe v0)))
-- _.IsLeftBolLoop.rightDivides
d_rightDivides_1162 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1162 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2798
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_2946 (coe v0)))
-- _.IsLeftBolLoop.∙-cong
d_'8729''45'cong_1174 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1174 = erased
-- _.IsLoop.//-cong
d_'47''47''45'cong_1182 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1182 = erased
-- _.IsLoop.\\-cong
d_'92''92''45'cong_1188 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1188 = erased
-- _.IsLoop.identity
d_identity_1194 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1194 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_2870 (coe v0)
-- _.IsLoop.isEquivalence
d_isEquivalence_1200 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1200 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2790
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868 (coe v0)))
-- _.IsLoop.isMagma
d_isMagma_1202 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1202 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2790
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868 (coe v0))
-- _.IsLoop.isQuasigroup
d_isQuasigroup_1206 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772
d_isQuasigroup_1206 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868 (coe v0)
-- _.IsLoop.leftDivides
d_leftDivides_1208 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1208 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2796
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868 (coe v0))
-- _.IsLoop.rightDivides
d_rightDivides_1218 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1218 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2798
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868 (coe v0))
-- _.IsLoop.∙-cong
d_'8729''45'cong_1230 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1230 = erased
-- _.IsMagma.isEquivalence
d_isEquivalence_1238 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1238 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_152 (coe v0)
-- _.IsMagma.∙-cong
d_'8729''45'cong_1252 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1252 = erased
-- _.IsMedialMagma.isEquivalence
d_isEquivalence_1260 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_328 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1260 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_336 (coe v0))
-- _.IsMedialMagma.isMagma
d_isMagma_1262 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1262 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_336 (coe v0)
-- _.IsMedialMagma.medial
d_medial_1266 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_328 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_medial_1266 = erased
-- _.IsMedialMagma.∙-cong
d_'8729''45'cong_1278 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_328 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1278 = erased
-- _.IsMiddleBolLoop.//-cong
d_'47''47''45'cong_1286 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1286 = erased
-- _.IsMiddleBolLoop.\\-cong
d_'92''92''45'cong_1292 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1292 = erased
-- _.IsMiddleBolLoop.identity
d_identity_1298 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1298 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_2870
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))
-- _.IsMiddleBolLoop.isEquivalence
d_isEquivalence_1304 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1304 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2790
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))))
-- _.IsMiddleBolLoop.isLoop
d_isLoop_1306 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854
d_isLoop_1306 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)
-- _.IsMiddleBolLoop.isMagma
d_isMagma_1308 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1308 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2790
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- _.IsMiddleBolLoop.isQuasigroup
d_isQuasigroup_1312 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772
d_isQuasigroup_1312 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))
-- _.IsMiddleBolLoop.leftDivides
d_leftDivides_1314 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1314 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2796
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- _.IsMiddleBolLoop.middleBol
d_middleBol_1320 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_middleBol_1320 = erased
-- _.IsMiddleBolLoop.rightDivides
d_rightDivides_1326 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1326 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2798
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- _.IsMiddleBolLoop.∙-cong
d_'8729''45'cong_1338 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1338 = erased
-- _.IsMonoid.assoc
d_assoc_1346 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1346 = erased
-- _.IsMonoid.identity
d_identity_1348 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1348 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_616 (coe v0)
-- _.IsMonoid.isEquivalence
d_isEquivalence_1354 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1354 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_614 (coe v0)))
-- _.IsMonoid.isMagma
d_isMagma_1356 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1356 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_614 (coe v0))
-- _.IsMonoid.isSemigroup
d_isSemigroup_1360 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_1360 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_614 (coe v0)
-- _.IsMonoid.∙-cong
d_'8729''45'cong_1374 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1374 = erased
-- _.IsMoufangLoop.//-cong
d_'47''47''45'cong_1382 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1382 = erased
-- _.IsMoufangLoop.\\-cong
d_'92''92''45'cong_1388 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1388 = erased
-- _.IsMoufangLoop.identical
d_identical_1394 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identical_1394 = erased
-- _.IsMoufangLoop.identity
d_identity_1396 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1396 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_2870
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_2946
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3112 (coe v0)))
-- _.IsMoufangLoop.isEquivalence
d_isEquivalence_1402 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1402 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2790
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLoop_2946
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3112 (coe v0)))))
-- _.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_1404 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_2932
d_isLeftBolLoop_1404 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3112 (coe v0)
-- _.IsMoufangLoop.isLoop
d_isLoop_1406 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854
d_isLoop_1406 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isLoop_2946
      (coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3112 (coe v0))
-- _.IsMoufangLoop.isMagma
d_isMagma_1408 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1408 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2790
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_2946
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3112 (coe v0))))
-- _.IsMoufangLoop.isQuasigroup
d_isQuasigroup_1412 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772
d_isQuasigroup_1412 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_2946
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3112 (coe v0)))
-- _.IsMoufangLoop.leftBol
d_leftBol_1414 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1414 = erased
-- _.IsMoufangLoop.leftDivides
d_leftDivides_1416 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1416 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2796
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_2946
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3112 (coe v0))))
-- _.IsMoufangLoop.rightBol
d_rightBol_1426 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_1426 = erased
-- _.IsMoufangLoop.rightDivides
d_rightDivides_1428 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1428 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2798
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_2946
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3112 (coe v0))))
-- _.IsMoufangLoop.∙-cong
d_'8729''45'cong_1440 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3096 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1440 = erased
-- _.IsNearSemiring.*-assoc
d_'42''45'assoc_1448 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1448 = erased
-- _.IsNearSemiring.*-cong
d_'42''45'cong_1450 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1450 = erased
-- _.IsNearSemiring.assoc
d_assoc_1460 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1460 = erased
-- _.IsNearSemiring.∙-cong
d_'8729''45'cong_1462 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1462 = erased
-- _.IsNearSemiring.identity
d_identity_1468 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1468 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1084 (coe v0))
-- _.IsNearSemiring.isMagma
d_isMagma_1474 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1474 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1084 (coe v0)))
-- _.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1476 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_'43''45'isMonoid_1476 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1084 (coe v0)
-- _.IsNearSemiring.isSemigroup
d_isSemigroup_1478 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_1478 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1084 (coe v0))
-- _.IsNearSemiring.distribʳ
d_distrib'691'_1482 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1482 = erased
-- _.IsNearSemiring.isEquivalence
d_isEquivalence_1484 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1484 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1084 (coe v0))))
-- _.IsNearSemiring.zeroˡ
d_zero'737'_1498 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1066 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1498 = erased
-- _.IsNearring.*-assoc
d_'42''45'assoc_1502 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1502 = erased
-- _.IsNearring.*-cong
d_'42''45'cong_1504 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1504 = erased
-- _.IsNearring.*-identity
d_'42''45'identity_1510 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1510 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2036
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0))
-- _.IsNearring.assoc
d_assoc_1522 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1522 = erased
-- _.IsNearring.∙-cong
d_'8729''45'cong_1524 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1524 = erased
-- _.IsNearring.identity
d_identity_1530 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1530 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0)))
-- _.IsNearring.+-inverse
d_'43''45'inverse_1536 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_1536 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'inverse_2386 (coe v0)
-- _.IsNearring.isMagma
d_isMagma_1542 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030
            (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0))))
-- _.IsNearring.+-isMonoid
d_'43''45'isMonoid_1544 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_'43''45'isMonoid_1544 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0))
-- _.IsNearring.isSemigroup
d_isSemigroup_1546 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_1546 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0)))
-- _.IsNearring.distrib
d_distrib_1550 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1550 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2038
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0))
-- _.IsNearring.isEquivalence
d_isEquivalence_1560 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1560 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0)))))
-- _.IsNearring.isQuasiring
d_isQuasiring_1564 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008
d_isQuasiring_1564 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0)
-- _.IsNearring.zero
d_zero_1576 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1576 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_2040
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2384 (coe v0))
-- _.IsNearring.⁻¹-cong
d_'8315''185''45'cong_1582 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2366 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1582 = erased
-- _.IsNonAssociativeRing.*-cong
d_'42''45'cong_1588 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1588 = erased
-- _.IsNonAssociativeRing.*-identity
d_'42''45'identity_1594 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1594 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2262 (coe v0)
-- _.IsNonAssociativeRing.assoc
d_assoc_1604 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1604 = erased
-- _.IsNonAssociativeRing.comm
d_comm_1606 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1606 = erased
-- _.IsNonAssociativeRing.∙-cong
d_'8729''45'cong_1608 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1608 = erased
-- _.IsNonAssociativeRing.identity
d_identity_1614 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1614 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_992
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2258
               (coe v0))))
-- _.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_1620 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980
d_'43''45'isAbelianGroup_1620 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2258
      (coe v0)
-- _.IsNonAssociativeRing.isGroup
d_isGroup_1628 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892
d_isGroup_1628 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_992
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2258
         (coe v0))
-- _.IsNonAssociativeRing.isMagma
d_isMagma_1634 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1634 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_906
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_992
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2258
                  (coe v0)))))
-- _.IsNonAssociativeRing.isMonoid
d_isMonoid_1636 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_1636 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_906
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_992
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2258
            (coe v0)))
-- _.IsNonAssociativeRing.isSemigroup
d_isSemigroup_1638 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_1638 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_992
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2258
               (coe v0))))
-- _.IsNonAssociativeRing.⁻¹-cong
d_'8315''185''45'cong_1642 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1642 = erased
-- _.IsNonAssociativeRing.inverse
d_inverse_1644 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1644 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_908
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_992
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2258
            (coe v0)))
-- _.IsNonAssociativeRing.distrib
d_distrib_1650 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1650 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2264 (coe v0)
-- _.IsNonAssociativeRing.isEquivalence
d_isEquivalence_1656 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1656 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_906
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_992
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2258
                     (coe v0))))))
-- _.IsNonAssociativeRing.zero
d_zero_1674 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2236 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1674 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2266 (coe v0)
-- _.IsQuasigroup.//-cong
d_'47''47''45'cong_1682 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1682 = erased
-- _.IsQuasigroup.\\-cong
d_'92''92''45'cong_1688 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1688 = erased
-- _.IsQuasigroup.isEquivalence
d_isEquivalence_1694 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1694 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2790 (coe v0))
-- _.IsQuasigroup.isMagma
d_isMagma_1696 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1696 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_2790 (coe v0)
-- _.IsQuasigroup.leftDivides
d_leftDivides_1700 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1700 v0
  = coe MAlonzo.Code.Algebra.Structures.d_leftDivides_2796 (coe v0)
-- _.IsQuasigroup.rightDivides
d_rightDivides_1710 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1710 v0
  = coe MAlonzo.Code.Algebra.Structures.d_rightDivides_2798 (coe v0)
-- _.IsQuasigroup.∙-cong
d_'8729''45'cong_1722 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1722 = erased
-- _.IsQuasiring.*-assoc
d_'42''45'assoc_1730 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1730 = erased
-- _.IsQuasiring.*-cong
d_'42''45'cong_1732 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1732 = erased
-- _.IsQuasiring.*-identity
d_'42''45'identity_1738 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1738 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2036 (coe v0)
-- _.IsQuasiring.assoc
d_assoc_1750 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1750 = erased
-- _.IsQuasiring.∙-cong
d_'8729''45'cong_1752 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1752 = erased
-- _.IsQuasiring.identity
d_identity_1758 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1758 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030 (coe v0))
-- _.IsQuasiring.isMagma
d_isMagma_1764 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1764 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030 (coe v0)))
-- _.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_1766 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_'43''45'isMonoid_1766 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030 (coe v0)
-- _.IsQuasiring.isSemigroup
d_isSemigroup_1768 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_1768 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030 (coe v0))
-- _.IsQuasiring.distrib
d_distrib_1772 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1772 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2038 (coe v0)
-- _.IsQuasiring.isEquivalence
d_isEquivalence_1782 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1782 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2030 (coe v0))))
-- _.IsQuasiring.zero
d_zero_1796 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2008 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1796 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2040 (coe v0)
-- _.IsRightBolLoop.//-cong
d_'47''47''45'cong_1804 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1804 = erased
-- _.IsRightBolLoop.\\-cong
d_'92''92''45'cong_1810 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1810 = erased
-- _.IsRightBolLoop.identity
d_identity_1816 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1816 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_2870
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3028 (coe v0))
-- _.IsRightBolLoop.isEquivalence
d_isEquivalence_1822 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1822 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2790
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3028 (coe v0))))
-- _.IsRightBolLoop.isLoop
d_isLoop_1824 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_2854
d_isLoop_1824 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3028 (coe v0)
-- _.IsRightBolLoop.isMagma
d_isMagma_1826 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1826 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2790
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3028 (coe v0)))
-- _.IsRightBolLoop.isQuasigroup
d_isQuasigroup_1830 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2772
d_isQuasigroup_1830 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3028 (coe v0))
-- _.IsRightBolLoop.leftDivides
d_leftDivides_1832 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1832 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2796
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3028 (coe v0)))
-- _.IsRightBolLoop.rightBol
d_rightBol_1842 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_1842 = erased
-- _.IsRightBolLoop.rightDivides
d_rightDivides_1844 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1844 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2798
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_2868
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3028 (coe v0)))
-- _.IsRightBolLoop.∙-cong
d_'8729''45'cong_1856 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3014 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1856 = erased
-- _.IsRing.*-assoc
d_'42''45'assoc_1866 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1866 = erased
-- _.IsRing.*-cong
d_'42''45'cong_1868 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1868 = erased
-- _.IsRing.*-identity
d_'42''45'identity_1874 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1874 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2506 (coe v0)
-- _.IsRing.assoc
d_assoc_1886 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1886 = erased
-- _.IsRing.comm
d_comm_1888 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1888 = erased
-- _.IsRing.∙-cong
d_'8729''45'cong_1890 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1890 = erased
-- _.IsRing.identity
d_identity_1896 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1896 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_1896 v5
du_identity_1896 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_1896 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_992
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
               (coe v0))))
-- _.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_1902 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980
d_'43''45'isAbelianGroup_1902 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
      (coe v0)
-- _.IsRing.isGroup
d_isGroup_1910 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892
d_isGroup_1910 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_1910 v5
du_isGroup_1910 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892
du_isGroup_1910 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_992
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
         (coe v0))
-- _.IsRing.isMagma
d_isMagma_1916 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_1916 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_1916 v5
du_isMagma_1916 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
du_isMagma_1916 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_906
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_992
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
                  (coe v0)))))
-- _.IsRing.isMonoid
d_isMonoid_1918 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_1918 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_1918 v5
du_isMonoid_1918 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
du_isMonoid_1918 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_906
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_992
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
            (coe v0)))
-- _.IsRing.isSemigroup
d_isSemigroup_1920 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_1920 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_1920 v5
du_isSemigroup_1920 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
du_isSemigroup_1920 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_992
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
               (coe v0))))
-- _.IsRing.⁻¹-cong
d_'8315''185''45'cong_1924 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1924 = erased
-- _.IsRing.inverse
d_inverse_1926 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1926 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_1926 v5
du_inverse_1926 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_1926 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_908
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_992
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
            (coe v0)))
-- _.IsRing.distrib
d_distrib_1932 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1932 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2508 (coe v0)
-- _.IsRing.isEquivalence
d_isEquivalence_1938 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1938 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_1938 v5
du_isEquivalence_1938 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_1938 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_906
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_992
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2500
                     (coe v0))))))
-- _.IsRing.isRingWithoutOne
d_isRingWithoutOne_1944 ::
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
   MAlonzo.Code.Agda.Builtin.Float.T_Float_6) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2478 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114
d_isRingWithoutOne_1944 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2510 v5
-- _.IsRingWithoutOne.*-assoc
d_'42''45'assoc_1976 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1976 = erased
-- _.IsRingWithoutOne.*-cong
d_'42''45'cong_1978 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1978 = erased
-- _.IsRingWithoutOne.assoc
d_assoc_1988 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1988 = erased
-- _.IsRingWithoutOne.comm
d_comm_1990 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1990 = erased
-- _.IsRingWithoutOne.∙-cong
d_'8729''45'cong_1992 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1992 = erased
-- _.IsRingWithoutOne.identity
d_identity_1998 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1998 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_992
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2132
               (coe v0))))
-- _.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2004 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_980
d_'43''45'isAbelianGroup_2004 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2132
      (coe v0)
-- _.IsRingWithoutOne.isGroup
d_isGroup_2012 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_892
d_isGroup_2012 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_992
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2132
         (coe v0))
-- _.IsRingWithoutOne.isMagma
d_isMagma_2018 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_2018 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_906
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_992
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2132
                  (coe v0)))))
-- _.IsRingWithoutOne.isMonoid
d_isMonoid_2020 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_2020 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_906
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_992
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2132
            (coe v0)))
-- _.IsRingWithoutOne.isSemigroup
d_isSemigroup_2022 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_2022 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_906
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_992
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2132
               (coe v0))))
-- _.IsRingWithoutOne.⁻¹-cong
d_'8315''185''45'cong_2026 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2026 = erased
-- _.IsRingWithoutOne.inverse
d_inverse_2028 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2028 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_908
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_992
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2132
            (coe v0)))
-- _.IsRingWithoutOne.distrib
d_distrib_2034 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2034 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2138 (coe v0)
-- _.IsRingWithoutOne.isEquivalence
d_isEquivalence_2040 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2114 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2040 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_906
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_992
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2132
                     (coe v0))))))
-- _.IsSelectiveMagma.isEquivalence
d_isEquivalence_2066 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2066 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_412 (coe v0))
-- _.IsSelectiveMagma.isMagma
d_isMagma_2068 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_404 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_2068 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_412 (coe v0)
-- _.IsSelectiveMagma.sel
d_sel_2076 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_404 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_2076 v0
  = coe MAlonzo.Code.Algebra.Structures.d_sel_414 (coe v0)
-- _.IsSelectiveMagma.∙-cong
d_'8729''45'cong_2084 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_404 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2084 = erased
-- _.IsSemigroup.assoc
d_assoc_2092 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2092 = erased
-- _.IsSemigroup.isEquivalence
d_isEquivalence_2094 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2094 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_448 (coe v0))
-- _.IsSemigroup.isMagma
d_isMagma_2096 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_2096 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_448 (coe v0)
-- _.IsSemigroup.∙-cong
d_'8729''45'cong_2110 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2110 = erased
-- _.IsSemimedialMagma.isEquivalence
d_isEquivalence_2118 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_364 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2118 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_372 (coe v0))
-- _.IsSemimedialMagma.isMagma
d_isMagma_2120 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_364 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_2120 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_372 (coe v0)
-- _.IsSemimedialMagma.semiMedial
d_semiMedial_2128 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_364 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_2128 v0
  = coe MAlonzo.Code.Algebra.Structures.d_semiMedial_374 (coe v0)
-- _.IsSemimedialMagma.∙-cong
d_'8729''45'cong_2140 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_364 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2140 = erased
-- _.IsSemiring.*-assoc
d_'42''45'assoc_2148 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2148 = erased
-- _.IsSemiring.*-cong
d_'42''45'cong_2150 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2150 = erased
-- _.IsSemiring.*-identity
d_'42''45'identity_2156 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2156 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1342
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe v0))
-- _.IsSemiring.assoc
d_assoc_2168 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2168 = erased
-- _.IsSemiring.comm
d_comm_2170 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2170 = erased
-- _.IsSemiring.∙-cong
d_'8729''45'cong_2172 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2172 = erased
-- _.IsSemiring.identity
d_identity_2178 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2178 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe v0))))
-- _.IsSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2186 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_'43''45'isCommutativeMonoid_2186 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe v0))
-- _.IsSemiring.isMagma
d_isMagma_2190 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_2190 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_664
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                  (coe v0)))))
-- _.IsSemiring.isMonoid
d_isMonoid_2192 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_2192 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
            (coe v0)))
-- _.IsSemiring.isSemigroup
d_isSemigroup_2194 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_2194 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
               (coe v0))))
-- _.IsSemiring.distrib
d_distrib_2198 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2198 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1344
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
         (coe v0))
-- _.IsSemiring.isEquivalence
d_isEquivalence_2204 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2204 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_664
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
                     (coe v0))))))
-- _.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2210 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316
d_isSemiringWithoutAnnihilatingZero_2210 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1432
      (coe v0)
-- _.IsSemiring.zero
d_zero_2224 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1418 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2224 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1434 (coe v0)
-- _.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2232 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2232 = erased
-- _.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2234 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2234 = erased
-- _.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2240 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2240 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1342 (coe v0)
-- _.IsSemiringWithoutAnnihilatingZero.assoc
d_assoc_2252 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2252 = erased
-- _.IsSemiringWithoutAnnihilatingZero.comm
d_comm_2254 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2254 = erased
-- _.IsSemiringWithoutAnnihilatingZero.∙-cong
d_'8729''45'cong_2256 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2256 = erased
-- _.IsSemiringWithoutAnnihilatingZero.identity
d_identity_2262 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2262 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_616
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe v0)))
-- _.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2270 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_'43''45'isCommutativeMonoid_2270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
      (coe v0)
-- _.IsSemiringWithoutAnnihilatingZero.isMagma
d_isMagma_2274 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_2274 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_448
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_664
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
               (coe v0))))
-- _.IsSemiringWithoutAnnihilatingZero.isMonoid
d_isMonoid_2276 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_2276 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
         (coe v0))
-- _.IsSemiringWithoutAnnihilatingZero.isSemigroup
d_isSemigroup_2278 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_440
d_isSemigroup_2278 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_664
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
            (coe v0)))
-- _.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2282 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2282 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1344 (coe v0)
-- _.IsSemiringWithoutAnnihilatingZero.isEquivalence
d_isEquivalence_2288 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1316 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2288 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_448
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_614
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_664
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1336
                  (coe v0)))))
-- _.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2308 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1146 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2308 = erased
-- _.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2310 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1146 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2310 = erased
-- _.IsSemiringWithoutOne.comm
d_comm_2320 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1146 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2320 = erased
-- _.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2324 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1146 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654
d_'43''45'isCommutativeMonoid_2324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1164
      (coe v0)
-- _.IsSemiringWithoutOne.isMonoid
d_isMonoid_2328 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1146 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_604
d_isMonoid_2328 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_664
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1164
         (coe v0))
-- _.IsSemiringWithoutOne.distrib
d_distrib_2332 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2332 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1170 (coe v0)
-- _.IsSemiringWithoutOne.zero
d_zero_2352 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2352 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1172 (coe v0)
-- _.IsUnitalMagma.identity
d_identity_2360 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_560 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2360 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_572 (coe v0)
-- _.IsUnitalMagma.isEquivalence
d_isEquivalence_2366 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_560 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2366 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_152
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_570 (coe v0))
-- _.IsUnitalMagma.isMagma
d_isMagma_2368 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_560 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_144
d_isMagma_2368 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_570 (coe v0)
-- _.IsUnitalMagma.∙-cong
d_'8729''45'cong_2382 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_560 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2382 = erased
-- Implementations.Real.+-*-isCommutativeRing
d_'43''45''42''45'isCommutativeRing_2388
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.+-*-isCommutativeRing"
-- Implementations.Real.0/N≡0
d_0'47'N'8801'0_2392
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.0/N\8801\&0"
-- Implementations.Real.cos0
d_cos0_2394
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.cos0"
-- Implementations.Real.sin0
d_sin0_2396
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.sin0"
-- Implementations.Real.cos-2πn
d_cos'45'2πn_2400
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.cos-2\960n"
-- Implementations.Real.sin-2πn
d_sin'45'2πn_2404
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.sin-2\960n"
-- Implementations.Real.ᵣ-distrib-*
d_'7523''45'distrib'45''42'_2410
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.\7523-distrib-*"
-- Implementations.Real.-distrib-*
d_'45'distrib'45''42'_2416
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.-distrib-*"
-- Implementations.Real.Nm/N≡m
d_Nm'47'N'8801'm_2422
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Real.Nm/N\8801m"
-- Implementations.Real.Base.realImplementation
d_realImplementation_2426 :: MAlonzo.Code.Real.T_Real_2
d_realImplementation_2426
  = coe
      MAlonzo.Code.Real.C_Real'46'constructor_38007
      MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24
      (coe
         MAlonzo.Code.Agda.Builtin.Float.d_primFloatACos_74
         (coe
            MAlonzo.Code.Agda.Builtin.Float.d_primFloatNegate_58
            (coe
               MAlonzo.Code.Agda.Builtin.Float.d_primNatToFloat_24
               (1 :: Integer))))
      MAlonzo.Code.Agda.Builtin.Float.d_primFloatPlus_48
      MAlonzo.Code.Agda.Builtin.Float.d_primFloatMinus_50
      MAlonzo.Code.Agda.Builtin.Float.d_primFloatTimes_52
      MAlonzo.Code.Agda.Builtin.Float.d_primFloatDiv_54
      MAlonzo.Code.Agda.Builtin.Float.d_primFloatNegate_58
      MAlonzo.Code.Agda.Builtin.Float.d_primFloatCos_68
      MAlonzo.Code.Agda.Builtin.Float.d_primFloatSin_66
      d_'43''45''42''45'isCommutativeRing_2388
-- Implementations.Real._.ℝ
d_ℝ_2472 :: ()
d_ℝ_2472 = erased
-- Implementations.Real.showℝ
d_showℝ_2474 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showℝ_2474
  = coe MAlonzo.Code.Agda.Builtin.Float.d_primShowFloat_46
