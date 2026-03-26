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

module MAlonzo.Code.Matrix.Simple.NonZ90Zero where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Matrix.Simple.Base
import qualified MAlonzo.Code.Matrix.Simple.Reshape
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Matrix.Simple.NonZero.#_
d_'35'__12 :: MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 -> Integer
d_'35'__12 = coe MAlonzo.Code.Matrix.Simple.Base.d_length_52
-- Matrix.Simple.NonZero._ᵗ
d__'7511'_14 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16
d__'7511'_14
  = coe
      MAlonzo.Code.Matrix.Simple.Reshape.d_recursive'45'transpose_274
-- Matrix.Simple.NonZero.NonZeroₛ
d_NonZero'8347'_16 a0 = ()
data T_NonZero'8347'_16
  = C_ι_18 MAlonzo.Code.Data.Nat.Base.T_NonZero_112 |
    C__'8855'__20 T_NonZero'8347'_16 T_NonZero'8347'_16
-- Matrix.Simple.NonZero.nonZeroDec
d_nonZeroDec_24 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_nonZeroDec_24 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe
                          C_ι_18
                          (coe
                             MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3581
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> let v3 = d_nonZeroDec_24 (coe v1) in
           coe
             (let v4 = d_nonZeroDec_24 (coe v2) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                     -> if coe v5
                          then case coe v6 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                   -> case coe v4 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> if coe v8
                                               then case coe v9 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v8)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                (coe C__'8855'__20 v7 v10))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v8)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          else coe
                                 seq (coe v6)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v5)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.NonZero.nonZeroₛ-s⇒nonZero-s
d_nonZero'8347''45's'8658'nonZero'45's_66 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_NonZero'8347'_16 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_nonZero'8347''45's'8658'nonZero'45's_66 ~v0 v1
  = du_nonZero'8347''45's'8658'nonZero'45's_66 v1
du_nonZero'8347''45's'8658'nonZero'45's_66 ::
  T_NonZero'8347'_16 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_nonZero'8347''45's'8658'nonZero'45's_66 v0
  = case coe v0 of
      C_ι_18 v2 -> coe v2
      C__'8855'__20 v3 v4
        -> coe MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0_3710
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.NonZero.nonZero-s⇒nonZeroₛ-s
d_nonZero'45's'8658'nonZero'8347''45's_94 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> T_NonZero'8347'_16
d_nonZero'45's'8658'nonZero'8347''45's_94 v0 v1
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v2 -> coe C_ι_18 v1
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v2 v3
        -> coe
             C__'8855'__20
             (d_nonZero'45's'8658'nonZero'8347''45's_94
                (coe v2)
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0'8658'm'8802'0_3720))
             (d_nonZero'45's'8658'nonZero'8347''45's_94
                (coe v3)
                (coe
                   MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0'8658'n'8802'0_3726))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.NonZero.nonZeroₛ-s⇒nonZeroₛ-sᵗ
d_nonZero'8347''45's'8658'nonZero'8347''45's'7511'_106 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_NonZero'8347'_16 -> T_NonZero'8347'_16
d_nonZero'8347''45's'8658'nonZero'8347''45's'7511'_106 v0 v1
  = case coe v1 of
      C_ι_18 v3 -> coe C_ι_18 v3
      C__'8855'__20 v4 v5
        -> case coe v0 of
             MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v6 v7
               -> coe
                    C__'8855'__20
                    (d_nonZero'8347''45's'8658'nonZero'8347''45's'7511'_106
                       (coe v7) (coe v5))
                    (d_nonZero'8347''45's'8658'nonZero'8347''45's'7511'_106
                       (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.NonZero.nonZeroₛ-sᵗ⇒nonZeroₛ-s
d_nonZero'8347''45's'7511''8658'nonZero'8347''45's_118 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_NonZero'8347'_16 -> T_NonZero'8347'_16
d_nonZero'8347''45's'7511''8658'nonZero'8347''45's_118 v0 v1
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v2
        -> case coe v1 of
             C_ι_18 v4 -> coe C_ι_18 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v2 v3
        -> case coe v1 of
             C__'8855'__20 v6 v7
               -> coe
                    C__'8855'__20
                    (d_nonZero'8347''45's'7511''8658'nonZero'8347''45's_118
                       (coe v2) (coe v7))
                    (d_nonZero'8347''45's'7511''8658'nonZero'8347''45's_118
                       (coe v3) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.NonZero.nonZeroₛ-s⇒nonZero-sᵗ
d_nonZero'8347''45's'8658'nonZero'45's'7511'_132 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_NonZero'8347'_16 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_nonZero'8347''45's'8658'nonZero'45's'7511'_132 ~v0 v1
  = du_nonZero'8347''45's'8658'nonZero'45's'7511'_132 v1
du_nonZero'8347''45's'8658'nonZero'45's'7511'_132 ::
  T_NonZero'8347'_16 -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_nonZero'8347''45's'8658'nonZero'45's'7511'_132 v0
  = case coe v0 of
      C_ι_18 v2 -> coe v2
      C__'8855'__20 v3 v4
        -> coe MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0_3710
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.NonZero.¬nonZeroₛ-s⇒¬nonZero-sᵗ
d_'172'nonZero'8347''45's'8658''172'nonZero'45's'7511'_144 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  (T_NonZero'8347'_16 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'nonZero'8347''45's'8658''172'nonZero'45's'7511'_144 = erased
-- Matrix.Simple.NonZero.nonZero-s⇒nonZero-sᵗ
d_nonZero'45's'8658'nonZero'45's'7511'_150 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_nonZero'45's'8658'nonZero'45's'7511'_150 v0 v1
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v2 -> coe v1
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v2 v3
        -> coe MAlonzo.Code.Data.Nat.Properties.du_m'42'n'8802'0_3710
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.NonZero.¬nonZero-sᵗ⇒¬nonZero-s
d_'172'nonZero'45's'7511''8658''172'nonZero'45's_162 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  (MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'nonZero'45's'7511''8658''172'nonZero'45's_162 = erased
-- Matrix.Simple.NonZero.¬nonZero-N⇒N≡0
d_'172'nonZero'45'N'8658'N'8801'0_180 ::
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172'nonZero'45'N'8658'N'8801'0_180 = erased
-- Matrix.Simple.NonZero.Fin0⇒⊥
d_Fin0'8658''8869'_188 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_Fin0'8658''8869'_188 = erased
-- Matrix.Simple.NonZero.¬nonZero-N⇒FinN-irrelevant
d_'172'nonZero'45'N'8658'FinN'45'irrelevant_194 ::
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172'nonZero'45'N'8658'FinN'45'irrelevant_194 = erased
-- Matrix.Simple.NonZero.¬nonZero-N⇒PosN-irrelevant
d_'172'nonZero'45'N'8658'PosN'45'irrelevant_212 ::
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172'nonZero'45'N'8658'PosN'45'irrelevant_212 = erased
-- Matrix.Simple.NonZero.nz≡nzₛ
d_nz'8801'nz'8347'_226 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  T_NonZero'8347'_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nz'8801'nz'8347'_226 = erased
-- Matrix.Simple.NonZero.nz≡nz
d_nz'8801'nz_240 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nz'8801'nz_240 = erased
-- Matrix.Simple.NonZero.nzₛ≡nzₛ
d_nz'8347''8801'nz'8347'_250 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  T_NonZero'8347'_16 ->
  T_NonZero'8347'_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nz'8347''8801'nz'8347'_250 = erased
