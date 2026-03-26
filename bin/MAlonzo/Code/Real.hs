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

module MAlonzo.Code.Real where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Structures

-- Real.Real
d_Real_2 = ()
data T_Real_2
  = C_Real'46'constructor_38007 (Integer -> AgdaAny) AgdaAny
                                (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                                (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                                (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624
-- Real._.IsCommutativeRing
d_IsCommutativeRing_44 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                       a13 a14
  = ()
-- Real.Real.ℝ
d_ℝ_2580 :: T_Real_2 -> ()
d_ℝ_2580 = erased
-- Real.Real._ᵣ
d__'7523'_2582 :: T_Real_2 -> Integer -> AgdaAny
d__'7523'_2582 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real.π
d_π_2584 :: T_Real_2 -> AgdaAny
d_π_2584 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real._+_
d__'43'__2586 :: T_Real_2 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__2586 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real._-_
d__'45'__2588 :: T_Real_2 -> AgdaAny -> AgdaAny -> AgdaAny
d__'45'__2588 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real._*_
d__'42'__2590 :: T_Real_2 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__2590 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real._/_
d__'47'__2592 :: T_Real_2 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47'__2592 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real.-_
d_'45'__2594 :: T_Real_2 -> AgdaAny -> AgdaAny
d_'45'__2594 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real.cos
d_cos_2596 :: T_Real_2 -> AgdaAny -> AgdaAny
d_cos_2596 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real.sin
d_sin_2598 :: T_Real_2 -> AgdaAny -> AgdaAny
d_sin_2598 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real.0ℝ
d_0ℝ_2600 :: T_Real_2 -> AgdaAny
d_0ℝ_2600 v0 = coe d__'7523'_2582 v0 (0 :: Integer)
-- Real.Real.-1ℝ
d_'45'1ℝ_2602 :: T_Real_2 -> AgdaAny
d_'45'1ℝ_2602 v0
  = coe d_'45'__2594 v0 (coe d__'7523'_2582 v0 (1 :: Integer))
-- Real.Real.1ℝ
d_1ℝ_2604 :: T_Real_2 -> AgdaAny
d_1ℝ_2604 v0 = coe d__'7523'_2582 v0 (1 :: Integer)
-- Real.Real.+-*-isCommutativeRing
d_'43''45''42''45'isCommutativeRing_5120 ::
  T_Real_2 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624
d_'43''45''42''45'isCommutativeRing_5120 v0
  = case coe v0 of
      C_Real'46'constructor_38007 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Real.Real.0/N≡0
d_0'47'N'8801'0_5124 ::
  T_Real_2 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'47'N'8801'0_5124 = erased
-- Real.Real.cos0
d_cos0_5126 ::
  T_Real_2 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cos0_5126 = erased
-- Real.Real.sin0
d_sin0_5128 ::
  T_Real_2 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sin0_5128 = erased
-- Real.Real.cos-2πn
d_cos'45'2πn_5132 ::
  T_Real_2 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cos'45'2πn_5132 = erased
-- Real.Real.sin-2πn
d_sin'45'2πn_5136 ::
  T_Real_2 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sin'45'2πn_5136 = erased
-- Real.Real.ᵣ-distrib-*
d_'7523''45'distrib'45''42'_5142 ::
  T_Real_2 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'7523''45'distrib'45''42'_5142 = erased
-- Real.Real.-distrib-*
d_'45'distrib'45''42'_5148 ::
  T_Real_2 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'45'distrib'45''42'_5148 = erased
-- Real.Real.Nm/N≡m
d_Nm'47'N'8801'm_5154 ::
  T_Real_2 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Nm'47'N'8801'm_5154 = erased
