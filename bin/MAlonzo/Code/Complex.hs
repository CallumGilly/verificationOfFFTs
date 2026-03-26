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

module MAlonzo.Code.Complex where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Nat.Base

-- Complex.Cplx
d_Cplx_2 = ()
data T_Cplx_2
  = C_Cplx'46'constructor_32759 (AgdaAny -> AgdaAny -> AgdaAny)
                                (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                (AgdaAny -> AgdaAny -> AgdaAny)
                                (Integer ->
                                 MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer -> AgdaAny)
                                AgdaAny AgdaAny
                                MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624
-- Complex._.IsCommutativeRing
d_IsCommutativeRing_40 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
  = ()
-- Complex.Cplx.ℂ
d_ℂ_2578 :: T_Cplx_2 -> ()
d_ℂ_2578 = erased
-- Complex.Cplx._+_
d__'43'__2580 :: T_Cplx_2 -> AgdaAny -> AgdaAny -> AgdaAny
d__'43'__2580 v0
  = case coe v0 of
      C_Cplx'46'constructor_32759 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Complex.Cplx._-_
d__'45'__2582 :: T_Cplx_2 -> AgdaAny -> AgdaAny -> AgdaAny
d__'45'__2582 v0
  = case coe v0 of
      C_Cplx'46'constructor_32759 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Complex.Cplx.-_
d_'45'__2584 :: T_Cplx_2 -> AgdaAny -> AgdaAny
d_'45'__2584 v0
  = case coe v0 of
      C_Cplx'46'constructor_32759 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Complex.Cplx._*_
d__'42'__2586 :: T_Cplx_2 -> AgdaAny -> AgdaAny -> AgdaAny
d__'42'__2586 v0
  = case coe v0 of
      C_Cplx'46'constructor_32759 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Complex.Cplx.-ω
d_'45'ω_2594 ::
  T_Cplx_2 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer -> AgdaAny
d_'45'ω_2594 v0
  = case coe v0 of
      C_Cplx'46'constructor_32759 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Complex.Cplx.0ℂ
d_0ℂ_2596 :: T_Cplx_2 -> AgdaAny
d_0ℂ_2596 v0
  = case coe v0 of
      C_Cplx'46'constructor_32759 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Complex.Cplx.1ℂ
d_1ℂ_2598 :: T_Cplx_2 -> AgdaAny
d_1ℂ_2598 v0
  = case coe v0 of
      C_Cplx'46'constructor_32759 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Complex.Cplx.+-*-isCommutativeRing
d_'43''45''42''45'isCommutativeRing_5114 ::
  T_Cplx_2 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2624
d_'43''45''42''45'isCommutativeRing_5114 v0
  = case coe v0 of
      C_Cplx'46'constructor_32759 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Complex.Cplx.ω-N-0
d_ω'45'N'45'0_5120 ::
  T_Cplx_2 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ω'45'N'45'0_5120 = erased
-- Complex.Cplx.ω-N-mN
d_ω'45'N'45'mN_5128 ::
  T_Cplx_2 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ω'45'N'45'mN_5128 = erased
-- Complex.Cplx.ω-r₁x-r₁y
d_ω'45'r'8321'x'45'r'8321'y_5140 ::
  T_Cplx_2 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ω'45'r'8321'x'45'r'8321'y_5140 = erased
-- Complex.Cplx.ω-N-k₀+k₁
d_ω'45'N'45'k'8320''43'k'8321'_5150 ::
  T_Cplx_2 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ω'45'N'45'k'8320''43'k'8321'_5150 = erased
