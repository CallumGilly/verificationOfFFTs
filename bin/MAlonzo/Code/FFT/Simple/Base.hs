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

module MAlonzo.Code.FFT.Simple.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Complex
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Matrix.Simple.Base
import qualified MAlonzo.Code.Matrix.Simple.NonZ90Zero
import qualified MAlonzo.Code.Matrix.Simple.Reshape
import qualified MAlonzo.Code.Matrix.Simple.Sum
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- FFT.Simple.Base.fin-nz
d_fin'45'nz_2422 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_fin'45'nz_2422 ~v0 ~v1 ~v2 = du_fin'45'nz_2422
du_fin'45'nz_2422 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_fin'45'nz_2422
  = coe
      MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3581
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- FFT.Simple.Base.pos⇒nz
d_pos'8658'nz_2428 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Matrix.Simple.NonZ90Zero.T_NonZero'8347'_16
d_pos'8658'nz_2428 ~v0 v1 v2 = du_pos'8658'nz_2428 v1 v2
du_pos'8658'nz_2428 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Matrix.Simple.NonZ90Zero.T_NonZero'8347'_16
du_pos'8658'nz_2428 v0 v1
  = case coe v1 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_28 v3
        -> coe
             MAlonzo.Code.Matrix.Simple.NonZ90Zero.C_ι_18
             (coe du_fin'45'nz_2422)
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v6 v7
               -> coe
                    MAlonzo.Code.Matrix.Simple.NonZ90Zero.C__'8855'__20
                    (coe du_pos'8658'nz_2428 (coe v6) (coe v4))
                    (coe du_pos'8658'nz_2428 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- FFT.Simple.Base.zs-nopos
d_zs'45'nopos_2436 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  (MAlonzo.Code.Matrix.Simple.NonZ90Zero.T_NonZero'8347'_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_zs'45'nopos_2436 = erased
-- FFT.Simple.Base.iota
d_iota_2450 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  Integer -> MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> Integer
d_iota_2450 ~v0 ~v1 v2 = du_iota_2450 v2
du_iota_2450 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> Integer
du_iota_2450 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_28 v2
        -> coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- FFT.Simple.Base.offset-prod
d_offset'45'prod_2454 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> Integer
d_offset'45'prod_2454 ~v0 v1 v2 v3
  = du_offset'45'prod_2454 v1 v2 v3
du_offset'45'prod_2454 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> Integer
du_offset'45'prod_2454 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v5 v6
        -> coe
             mulInt
             (coe
                du_iota_2450
                (coe
                   MAlonzo.Code.Matrix.Simple.Reshape.d__'10216'_'10217'_44 (coe v0)
                   (coe
                      MAlonzo.Code.Matrix.Simple.Base.C_ι_18
                      (coe MAlonzo.Code.Matrix.Simple.Base.d_length_52 (coe v0)))
                   (coe v5)
                   (coe MAlonzo.Code.Matrix.Simple.Reshape.d_'9839'_342 (coe v0))))
             (coe
                du_iota_2450
                (coe
                   MAlonzo.Code.Matrix.Simple.Reshape.d__'10216'_'10217'_44 (coe v1)
                   (coe
                      MAlonzo.Code.Matrix.Simple.Base.C_ι_18
                      (coe MAlonzo.Code.Matrix.Simple.Base.d_length_52 (coe v1)))
                   (coe v6)
                   (coe MAlonzo.Code.Matrix.Simple.Reshape.d_'9839'_342 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- FFT.Simple.Base.twiddles′
d_twiddles'8242'_2460 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  Integer ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
d_twiddles'8242'_2460 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Complex.d_'45'ω_2594 v0
      (addInt (coe (1 :: Integer)) (coe v3)) erased
      (coe
         du_offset'45'prod_2454 (coe v1) (coe v2)
         (coe MAlonzo.Code.Matrix.Simple.Base.C__'8855'__30 v4 v5))
-- FFT.Simple.Base.twiddles
d_twiddles_2468 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
d_twiddles_2468 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Matrix.Simple.NonZ90Zero.d_nonZeroDec_24 (coe v1) in
    coe
      (let v5
             = MAlonzo.Code.Matrix.Simple.NonZ90Zero.d_nonZeroDec_24 (coe v2) in
       coe
         (case coe v4 of
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
              -> if coe v6
                   then coe
                          seq (coe v7)
                          (case coe v5 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                               -> if coe v8
                                    then coe
                                           seq (coe v9)
                                           (coe
                                              MAlonzo.Code.Complex.d_'45'ω_2594 v0
                                              (MAlonzo.Code.Matrix.Simple.Base.d_length_52
                                                 (coe
                                                    MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
                                                    (coe v1) (coe v2)))
                                              erased
                                              (coe
                                                 du_offset'45'prod_2454 (coe v1) (coe v2) (coe v3)))
                                    else (let v10
                                                = seq
                                                    (coe v9)
                                                    (coe
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                 -> if coe v11
                                                      then coe
                                                             seq (coe v12)
                                                             (coe
                                                                MAlonzo.Code.Complex.d_'45'ω_2594 v0
                                                                (MAlonzo.Code.Matrix.Simple.Base.d_length_52
                                                                   (coe
                                                                      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
                                                                      (coe v1) (coe v2)))
                                                                erased
                                                                (coe
                                                                   du_offset'45'prod_2454 (coe v1)
                                                                   (coe v2) (coe v3)))
                                                      else coe
                                                             seq (coe v12)
                                                             (coe
                                                                MAlonzo.Code.Data.Empty.du_'8869''45'elim_14)
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else (let v8
                               = seq
                                   (coe v7)
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                      (coe v6)
                                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                -> if coe v9
                                     then coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Complex.d_'45'ω_2594 v0
                                               (MAlonzo.Code.Matrix.Simple.Base.d_length_52
                                                  (coe
                                                     MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
                                                     (coe v1) (coe v2)))
                                               erased
                                               (coe
                                                  du_offset'45'prod_2454 (coe v1) (coe v2)
                                                  (coe v3)))
                                     else coe
                                            seq (coe v10)
                                            (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14)
                              _ -> MAlonzo.RTE.mazUnreachableError))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- FFT.Simple.Base.DFT′
d_DFT'8242'_2498 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
d_DFT'8242'_2498 v0 v1 v2
  = let v3
          = MAlonzo.Code.Data.Nat.Properties.d_nonZero'63'_2522 (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (case coe v1 of
                          0 -> coe (\ v6 -> MAlonzo.RTE.mazUnreachableError)
                          _ -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    (\ v7 ->
                                       coe
                                         MAlonzo.Code.Matrix.Simple.Sum.du_sum_162
                                         (coe MAlonzo.Code.Complex.d__'43'__2580 (coe v0))
                                         (coe MAlonzo.Code.Complex.d_0ℂ_2596 (coe v0)) (coe v1)
                                         (coe
                                            (\ v8 ->
                                               coe
                                                 MAlonzo.Code.Complex.d__'42'__2586 v0 (coe v2 v8)
                                                 (d_twiddles'8242'_2460
                                                    (coe v0)
                                                    (coe
                                                       MAlonzo.Code.Matrix.Simple.Base.C_ι_18
                                                       (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Matrix.Simple.Base.C_ι_18
                                                       (coe v1))
                                                    (coe v6) (coe v7) (coe v8)))))))
                else coe
                       seq (coe v5)
                       (coe
                          (\ v6 ->
                             seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- FFT.Simple.Base.DFT
d_DFT_2530 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
d_DFT_2530 v0 v1 v2
  = let v3
          = MAlonzo.Code.Data.Nat.Properties.d_nonZero'63'_2522 (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          (\ v6 ->
                             coe
                               MAlonzo.Code.Matrix.Simple.Sum.du_sum_162
                               (coe MAlonzo.Code.Complex.d__'43'__2580 (coe v0))
                               (coe MAlonzo.Code.Complex.d_0ℂ_2596 (coe v0)) (coe v1)
                               (coe
                                  (\ v7 ->
                                     coe
                                       MAlonzo.Code.Complex.d__'42'__2586 v0 (coe v2 v7)
                                       (coe
                                          MAlonzo.Code.Complex.d_'45'ω_2594 v0 v1 erased
                                          (mulInt
                                             (coe du_iota_2450 (coe v7))
                                             (coe du_iota_2450 (coe v6))))))))
                else coe
                       seq (coe v5)
                       (coe
                          (\ v6 ->
                             seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- FFT.Simple.Base.FFT
d_FFT_2562 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
d_FFT_2562 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v3
        -> coe d_DFT_2530 (coe v0) (coe v3) (coe v2)
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v3 v4
        -> coe
             MAlonzo.Code.Matrix.Simple.Reshape.du_reshape_88
             (coe
                MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
                (coe
                   MAlonzo.Code.Matrix.Simple.Reshape.d_recursive'45'transpose_274
                   (coe v3))
                (coe
                   MAlonzo.Code.Matrix.Simple.Reshape.d_recursive'45'transpose_274
                   (coe v4)))
             (coe
                MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
                (coe
                   MAlonzo.Code.Matrix.Simple.Reshape.d_recursive'45'transpose_274
                   (coe v4))
                (coe
                   MAlonzo.Code.Matrix.Simple.Reshape.d_recursive'45'transpose_274
                   (coe v3)))
             (coe MAlonzo.Code.Matrix.Simple.Reshape.C_swap_38)
             (coe
                MAlonzo.Code.Matrix.Simple.Base.du_mapLeft_98
                (coe d_FFT_2562 (coe v0) (coe v4))
                (coe
                   MAlonzo.Code.Matrix.Simple.Reshape.du_reshape_88
                   (coe
                      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v4)
                      (coe
                         MAlonzo.Code.Matrix.Simple.Reshape.d_recursive'45'transpose_274
                         (coe v3)))
                   (coe
                      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
                      (coe
                         MAlonzo.Code.Matrix.Simple.Reshape.d_recursive'45'transpose_274
                         (coe v3))
                      (coe v4))
                   (coe MAlonzo.Code.Matrix.Simple.Reshape.C_swap_38)
                   (coe
                      MAlonzo.Code.Matrix.Simple.Base.du_zipWith_168
                      (coe MAlonzo.Code.Complex.d__'42'__2586 (coe v0))
                      (coe
                         MAlonzo.Code.Matrix.Simple.Base.du_mapLeft_98
                         (coe d_FFT_2562 (coe v0) (coe v3))
                         (coe
                            MAlonzo.Code.Matrix.Simple.Reshape.du_reshape_88 (coe v1)
                            (coe
                               MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v4) (coe v3))
                            (coe MAlonzo.Code.Matrix.Simple.Reshape.C_swap_38) (coe v2)))
                      (coe
                         d_twiddles_2468 (coe v0) (coe v4)
                         (coe
                            MAlonzo.Code.Matrix.Simple.Reshape.d_recursive'45'transpose_274
                            (coe v3))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- FFT.Simple.Base.RFFT
d_RFFT_2582 ::
  MAlonzo.Code.Complex.T_Cplx_2 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
d_RFFT_2582 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v3
        -> coe d_DFT_2530 (coe v0) (coe v3) (coe v2)
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v3 v4
        -> coe
             MAlonzo.Code.Matrix.Simple.Reshape.du_reshape_88 (coe v1) (coe v1)
             (coe
                MAlonzo.Code.Matrix.Simple.Reshape.C__'8729'__30
                (coe
                   MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v4) (coe v3))
                (MAlonzo.Code.Matrix.Simple.Reshape.d_CM_396 (coe v4) (coe v3))
                (coe MAlonzo.Code.Matrix.Simple.Reshape.C_swap_38))
             (coe
                MAlonzo.Code.Matrix.Simple.Base.du_mapLeft_98
                (coe d_RFFT_2582 (coe v0) (coe v4))
                (coe
                   MAlonzo.Code.Matrix.Simple.Reshape.du_reshape_88
                   (coe
                      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v4) (coe v3))
                   (coe v1) (coe MAlonzo.Code.Matrix.Simple.Reshape.C_swap_38)
                   (coe
                      MAlonzo.Code.Matrix.Simple.Base.du_zipWith_168
                      (coe MAlonzo.Code.Complex.d__'42'__2586 (coe v0))
                      (coe
                         MAlonzo.Code.Matrix.Simple.Base.du_mapLeft_98
                         (coe d_RFFT_2582 (coe v0) (coe v3))
                         (coe
                            MAlonzo.Code.Matrix.Simple.Reshape.du_reshape_88 (coe v1)
                            (coe
                               MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 (coe v4) (coe v3))
                            (coe MAlonzo.Code.Matrix.Simple.Reshape.C_swap_38) (coe v2)))
                      (coe d_twiddles_2468 (coe v0) (coe v4) (coe v3)))))
      _ -> MAlonzo.RTE.mazUnreachableError
