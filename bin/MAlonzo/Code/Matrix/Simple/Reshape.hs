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

module MAlonzo.Code.Matrix.Simple.Reshape where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Matrix.Simple.Base

-- Matrix.Simple.Reshape.Reshape
d_Reshape_26 a0 a1 = ()
data T_Reshape_26
  = C_eq_28 |
    C__'8729'__30 MAlonzo.Code.Matrix.Simple.Base.T_Shape_16
                  T_Reshape_26 T_Reshape_26 |
    C__'8853'__32 T_Reshape_26 T_Reshape_26 | C_split_34 | C_flat_36 |
    C_swap_38 | C_asso'8343'_40 | C_asso'7523'_42
-- Matrix.Simple.Reshape._⟨_⟩
d__'10216'_'10217'_44 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  T_Reshape_26 -> MAlonzo.Code.Matrix.Simple.Base.T_Position_26
d__'10216'_'10217'_44 v0 v1 v2 v3
  = case coe v3 of
      C_eq_28 -> coe v2
      C__'8729'__30 v4 v7 v8
        -> coe
             d__'10216'_'10217'_44 (coe v4) (coe v1)
             (coe d__'10216'_'10217'_44 (coe v0) (coe v4) (coe v2) (coe v7))
             (coe v8)
      C__'8853'__32 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v12 v13
                      -> case coe v2 of
                           MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v16 v17
                             -> coe
                                  MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30
                                  (d__'10216'_'10217'_44 (coe v10) (coe v12) (coe v16) (coe v8))
                                  (d__'10216'_'10217'_44 (coe v11) (coe v13) (coe v17) (coe v9))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_split_34
        -> case coe v0 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v8
                      -> case coe v2 of
                           MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v11 v12
                             -> case coe v11 of
                                  MAlonzo.Code.Matrix.Simple.Base.C_ι_28 v14
                                    -> case coe v12 of
                                         MAlonzo.Code.Matrix.Simple.Base.C_ι_28 v16
                                           -> coe
                                                MAlonzo.Code.Matrix.Simple.Base.C_ι_28
                                                (coe
                                                   MAlonzo.Code.Data.Fin.Base.du_combine_226
                                                   (coe v8) (coe v14) (coe v16))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_flat_36
        -> case coe v1 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v8
                      -> case coe v2 of
                           MAlonzo.Code.Matrix.Simple.Base.C_ι_28 v10
                             -> coe
                                  MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30
                                  (coe
                                     MAlonzo.Code.Matrix.Simple.Base.C_ι_28
                                     (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           MAlonzo.Code.Data.Fin.Base.du_remQuot_208 (coe v8)
                                           (coe v10))))
                                  (coe
                                     MAlonzo.Code.Matrix.Simple.Base.C_ι_28
                                     (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                        (coe
                                           MAlonzo.Code.Data.Fin.Base.du_remQuot_208 (coe v8)
                                           (coe v10))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_swap_38
        -> case coe v2 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v8 v9
               -> coe MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v9 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_asso'8343'_40
        -> case coe v2 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v13 v14
                      -> coe
                           MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30
                           (coe MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v9 v13) v14
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_asso'7523'_42
        -> case coe v2 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v13 v14
                      -> coe
                           MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v13
                           (coe MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v14 v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Reshape.reshape
d_reshape_88 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  () ->
  T_Reshape_26 ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
d_reshape_88 v0 v1 ~v2 v3 v4 v5 = du_reshape_88 v0 v1 v3 v4 v5
du_reshape_88 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_Reshape_26 ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
du_reshape_88 v0 v1 v2 v3 v4
  = coe
      v3 (d__'10216'_'10217'_44 (coe v1) (coe v0) (coe v4) (coe v2))
-- Matrix.Simple.Reshape.rev
d_rev_96 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_Reshape_26 -> T_Reshape_26
d_rev_96 v0 v1 v2
  = case coe v2 of
      C_eq_28 -> coe C_eq_28
      C__'8729'__30 v3 v6 v7
        -> coe
             C__'8729'__30 v3 (d_rev_96 (coe v0) (coe v3) (coe v7))
             (d_rev_96 (coe v3) (coe v1) (coe v6))
      C__'8853'__32 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v11 v12
                      -> coe
                           C__'8853'__32 (d_rev_96 (coe v9) (coe v11) (coe v7))
                           (d_rev_96 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_split_34 -> coe C_flat_36
      C_flat_36 -> coe C_split_34
      C_swap_38 -> coe C_swap_38
      C_asso'8343'_40 -> coe C_asso'7523'_42
      C_asso'7523'_42 -> coe C_asso'8343'_40
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Reshape.rev-eq
d_rev'45'eq_110 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_Reshape_26 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rev'45'eq_110 = erased
-- Matrix.Simple.Reshape.rev-rev
d_rev'45'rev_198 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_Reshape_26 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rev'45'rev_198 = erased
-- Matrix.Simple.Reshape.transpose
d_transpose_250 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16
d_transpose_250 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1 -> coe v0
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> coe
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Reshape.transposeᵣ
d_transpose'7523'_258 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> T_Reshape_26
d_transpose'7523'_258 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1 -> coe C_eq_28
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> coe C_swap_38
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Reshape.transp-inv
d_transp'45'inv_266 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_transp'45'inv_266 = erased
-- Matrix.Simple.Reshape.recursive-transpose
d_recursive'45'transpose_274 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16
d_recursive'45'transpose_274 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1 -> coe v0
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> coe
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
             (coe d_recursive'45'transpose_274 (coe v2))
             (coe d_recursive'45'transpose_274 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Reshape.recursive-transposeᵣ
d_recursive'45'transpose'7523'_282 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> T_Reshape_26
d_recursive'45'transpose'7523'_282 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1 -> coe C_eq_28
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> coe
             C__'8729'__30
             (coe
                MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
                (coe d_recursive'45'transpose_274 (coe v1))
                (coe d_recursive'45'transpose_274 (coe v2)))
             (coe C_swap_38)
             (coe
                C__'8853'__32 (d_recursive'45'transpose'7523'_282 (coe v1))
                (d_recursive'45'transpose'7523'_282 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Reshape.recursive-transpose-inv
d_recursive'45'transpose'45'inv_290 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_recursive'45'transpose'45'inv_290 = erased
-- Matrix.Simple.Reshape.recursive-transpose-invᵣ
d_recursive'45'transpose'45'inv'7523'_306 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> T_Reshape_26
d_recursive'45'transpose'45'inv'7523'_306 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1 -> coe C_eq_28
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> coe
             C__'8853'__32 (d_recursive'45'transpose'45'inv'7523'_306 (coe v1))
             (d_recursive'45'transpose'45'inv'7523'_306 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Reshape.|s|≡|sᵗ|
d_'124's'124''8801''124's'7511''124'_314 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'124's'124''8801''124's'7511''124'_314 = erased
-- Matrix.Simple.Reshape.♭
d_'9837'_334 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> T_Reshape_26
d_'9837'_334 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1 -> coe C_eq_28
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> coe
             C__'8729'__30
             (coe
                MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
                (coe
                   MAlonzo.Code.Matrix.Simple.Base.C_ι_18
                   (coe MAlonzo.Code.Matrix.Simple.Base.d_length_52 (coe v1)))
                (coe
                   MAlonzo.Code.Matrix.Simple.Base.C_ι_18
                   (coe MAlonzo.Code.Matrix.Simple.Base.d_length_52 (coe v2))))
             (coe C_flat_36)
             (coe C__'8853'__32 (d_'9837'_334 (coe v1)) (d_'9837'_334 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Reshape.♯
d_'9839'_342 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> T_Reshape_26
d_'9839'_342 v0
  = coe
      d_rev_96 (coe v0)
      (coe
         MAlonzo.Code.Matrix.Simple.Base.C_ι_18
         (coe MAlonzo.Code.Matrix.Simple.Base.d_length_52 (coe v0)))
      (coe d_'9837'_334 (coe v0))
-- Matrix.Simple.Reshape.reindex
d_reindex_344 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Reshape_26
d_reindex_344 ~v0 ~v1 ~v2 = du_reindex_344
du_reindex_344 :: T_Reshape_26
du_reindex_344 = coe C_eq_28
-- Matrix.Simple.Reshape.reindex-cast
d_reindex'45'cast_358 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reindex'45'cast_358 = erased
-- Matrix.Simple.Reshape.ext
d_ext_374 ::
  Integer ->
  () ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext_374 = erased
-- Matrix.Simple.Reshape.reindex-reindex
d_reindex'45'reindex_384 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reindex'45'reindex_384 = erased
-- Matrix.Simple.Reshape.flatten-reindex
d_flatten'45'reindex_388 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> T_Reshape_26
d_flatten'45'reindex_388 v0
  = coe
      C__'8729'__30
      (coe
         MAlonzo.Code.Matrix.Simple.Base.C_ι_18
         (coe MAlonzo.Code.Matrix.Simple.Base.d_length_52 (coe v0)))
      (coe du_reindex_344) (d_'9837'_334 (coe v0))
-- Matrix.Simple.Reshape.CM
d_CM_396 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> T_Reshape_26
d_CM_396 v0 v1
  = coe
      C__'8729'__30
      (coe
         MAlonzo.Code.Matrix.Simple.Base.C_ι_18
         (coe
            MAlonzo.Code.Matrix.Simple.Base.d_length_52
            (coe
               MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v1) (coe v0))))
      (d_'9839'_342
         (coe
            MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v1) (coe v0)))
      (coe
         C__'8729'__30
         (coe
            MAlonzo.Code.Matrix.Simple.Base.C_ι_18
            (coe
               mulInt (coe MAlonzo.Code.Matrix.Simple.Base.d_length_52 (coe v0))
               (coe MAlonzo.Code.Matrix.Simple.Base.d_length_52 (coe v1))))
         (coe du_reindex_344)
         (d_'9837'_334
            (coe
               MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v0) (coe v1))))
-- Matrix.Simple.Reshape.CMᵗ
d_CM'7511'_404 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> T_Reshape_26
d_CM'7511'_404 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1 -> coe C_eq_28
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> coe
             C__'8729'__30
             (coe
                MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v2) (coe v1))
             (coe
                C__'8853'__32 (d_CM'7511'_404 (coe v2)) (d_CM'7511'_404 (coe v1)))
             (d_CM_396 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
