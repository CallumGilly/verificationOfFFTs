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

module MAlonzo.Code.Implementations.Complex where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Complex
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Real

-- Implementations.Complex.Base.ℂ₁
d_ℂ'8321'_60 a0 = ()
data T_ℂ'8321'_60 = C__'43'_i_70 AgdaAny AgdaAny
-- Implementations.Complex.Base.ℂ₁.real-component
d_real'45'component_66 :: T_ℂ'8321'_60 -> AgdaAny
d_real'45'component_66 v0
  = case coe v0 of
      C__'43'_i_70 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Implementations.Complex.Base.ℂ₁.imaginary-component
d_imaginary'45'component_68 :: T_ℂ'8321'_60 -> AgdaAny
d_imaginary'45'component_68 v0
  = case coe v0 of
      C__'43'_i_70 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Implementations.Complex.Base.0ℂ
d_0ℂ_72 :: MAlonzo.Code.Real.T_Real_2 -> T_ℂ'8321'_60
d_0ℂ_72 v0
  = coe
      C__'43'_i_70
      (coe MAlonzo.Code.Real.d__'7523'_2582 v0 (0 :: Integer))
      (coe MAlonzo.Code.Real.d__'7523'_2582 v0 (0 :: Integer))
-- Implementations.Complex.Base.-1ℂ
d_'45'1ℂ_74 :: MAlonzo.Code.Real.T_Real_2 -> T_ℂ'8321'_60
d_'45'1ℂ_74 v0
  = coe
      C__'43'_i_70
      (coe
         MAlonzo.Code.Real.d_'45'__2594 v0
         (coe MAlonzo.Code.Real.d__'7523'_2582 v0 (1 :: Integer)))
      (coe MAlonzo.Code.Real.d__'7523'_2582 v0 (0 :: Integer))
-- Implementations.Complex.Base.1ℂ
d_1ℂ_76 :: MAlonzo.Code.Real.T_Real_2 -> T_ℂ'8321'_60
d_1ℂ_76 v0
  = coe
      C__'43'_i_70
      (coe MAlonzo.Code.Real.d__'7523'_2582 v0 (1 :: Integer))
      (coe MAlonzo.Code.Real.d__'7523'_2582 v0 (0 :: Integer))
-- Implementations.Complex.Base._+_
d__'43'__78 ::
  MAlonzo.Code.Real.T_Real_2 ->
  T_ℂ'8321'_60 -> T_ℂ'8321'_60 -> T_ℂ'8321'_60
d__'43'__78 v0 v1 v2
  = case coe v1 of
      C__'43'_i_70 v3 v4
        -> case coe v2 of
             C__'43'_i_70 v5 v6
               -> coe
                    C__'43'_i_70 (coe MAlonzo.Code.Real.d__'43'__2586 v0 v3 v5)
                    (coe MAlonzo.Code.Real.d__'43'__2586 v0 v4 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Implementations.Complex.Base._-_
d__'45'__88 ::
  MAlonzo.Code.Real.T_Real_2 ->
  T_ℂ'8321'_60 -> T_ℂ'8321'_60 -> T_ℂ'8321'_60
d__'45'__88 v0 v1 v2
  = case coe v1 of
      C__'43'_i_70 v3 v4
        -> case coe v2 of
             C__'43'_i_70 v5 v6
               -> coe
                    C__'43'_i_70 (coe MAlonzo.Code.Real.d__'45'__2588 v0 v3 v5)
                    (coe MAlonzo.Code.Real.d__'45'__2588 v0 v4 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Implementations.Complex.Base.-_
d_'45'__98 ::
  MAlonzo.Code.Real.T_Real_2 -> T_ℂ'8321'_60 -> T_ℂ'8321'_60
d_'45'__98 v0 v1
  = case coe v1 of
      C__'43'_i_70 v2 v3
        -> coe
             C__'43'_i_70 (coe MAlonzo.Code.Real.d_'45'__2594 v0 v2)
             (coe MAlonzo.Code.Real.d_'45'__2594 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Implementations.Complex.Base._*_
d__'42'__104 ::
  MAlonzo.Code.Real.T_Real_2 ->
  T_ℂ'8321'_60 -> T_ℂ'8321'_60 -> T_ℂ'8321'_60
d__'42'__104 v0 v1 v2
  = case coe v1 of
      C__'43'_i_70 v3 v4
        -> case coe v2 of
             C__'43'_i_70 v5 v6
               -> coe
                    C__'43'_i_70
                    (coe
                       MAlonzo.Code.Real.d__'45'__2588 v0
                       (coe MAlonzo.Code.Real.d__'42'__2590 v0 v3 v5)
                       (coe MAlonzo.Code.Real.d__'42'__2590 v0 v4 v6))
                    (coe
                       MAlonzo.Code.Real.d__'43'__2586 v0
                       (coe MAlonzo.Code.Real.d__'42'__2590 v0 v3 v6)
                       (coe MAlonzo.Code.Real.d__'42'__2590 v0 v4 v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Implementations.Complex.Base.fromℝ
d_fromℝ_114 ::
  MAlonzo.Code.Real.T_Real_2 -> AgdaAny -> T_ℂ'8321'_60
d_fromℝ_114 v0 v1
  = coe
      C__'43'_i_70 (coe v1)
      (coe MAlonzo.Code.Real.d__'7523'_2582 v0 (0 :: Integer))
-- Implementations.Complex.Base.ℂfromℕ
d_ℂfromℕ_118 ::
  MAlonzo.Code.Real.T_Real_2 -> Integer -> T_ℂ'8321'_60
d_ℂfromℕ_118 v0 v1
  = coe
      d_fromℝ_114 (coe v0) (coe MAlonzo.Code.Real.d__'7523'_2582 v0 v1)
-- Implementations.Complex.Base.e^i_
d_e'94'i__120 ::
  MAlonzo.Code.Real.T_Real_2 -> AgdaAny -> T_ℂ'8321'_60
d_e'94'i__120 v0 v1
  = coe
      C__'43'_i_70 (coe MAlonzo.Code.Real.d_cos_2596 v0 v1)
      (coe MAlonzo.Code.Real.d_sin_2598 v0 v1)
-- Implementations.Complex.Base.-ω
d_'45'ω_130 ::
  MAlonzo.Code.Real.T_Real_2 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 -> Integer -> T_ℂ'8321'_60
d_'45'ω_130 v0 v1 ~v2 v3 = du_'45'ω_130 v0 v1 v3
du_'45'ω_130 ::
  MAlonzo.Code.Real.T_Real_2 -> Integer -> Integer -> T_ℂ'8321'_60
du_'45'ω_130 v0 v1 v2
  = coe
      d_e'94'i__120 (coe v0)
      (coe
         MAlonzo.Code.Real.d__'47'__2592 v0
         (coe
            MAlonzo.Code.Real.d__'42'__2590 v0
            (coe
               MAlonzo.Code.Real.d__'42'__2590 v0
               (coe
                  MAlonzo.Code.Real.d_'45'__2594 v0
                  (coe MAlonzo.Code.Real.d__'7523'_2582 v0 (2 :: Integer)))
               (MAlonzo.Code.Real.d_π_2584 (coe v0)))
            (coe MAlonzo.Code.Real.d__'7523'_2582 v0 v2))
         (coe MAlonzo.Code.Real.d__'7523'_2582 v0 v1))
-- Implementations.Complex.Base.ω-N-0
d_ω'45'N'45'0_140 ::
  MAlonzo.Code.Real.T_Real_2 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ω'45'N'45'0_140 = erased
-- Implementations.Complex.Base.ω-N-mN
d_ω'45'N'45'mN_168 ::
  MAlonzo.Code.Real.T_Real_2 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ω'45'N'45'mN_168 = erased
-- Implementations.Complex.Base.isCommutativeRing
d_isCommutativeRing_206
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Complex.Base.isCommutativeRing"
-- Implementations.Complex.Base.ω-r₁x-r₁y
d_ω'45'r'8321'x'45'r'8321'y_218
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Complex.Base.\969-r\8321x-r\8321y"
-- Implementations.Complex.Base.ω-N-k₀+k₁
d_ω'45'N'45'k'8320''43'k'8321'_228
  = error
      "MAlonzo Runtime Error: postulate evaluated: Implementations.Complex.Base.\969-N-k\8320+k\8321"
-- Implementations.Complex.Base.complexImplementation
d_complexImplementation_230 ::
  MAlonzo.Code.Real.T_Real_2 -> MAlonzo.Code.Complex.T_Cplx_2
d_complexImplementation_230 v0
  = coe
      MAlonzo.Code.Complex.C_Cplx'46'constructor_32759
      (d__'43'__78 (coe v0)) (d__'45'__88 (coe v0)) (d_'45'__98 (coe v0))
      (d__'42'__104 (coe v0))
      (\ v1 v2 v3 -> coe du_'45'ω_130 (coe v0) v1 v3) (d_0ℂ_72 (coe v0))
      (d_1ℂ_76 (coe v0)) (coe d_isCommutativeRing_206 v0)
