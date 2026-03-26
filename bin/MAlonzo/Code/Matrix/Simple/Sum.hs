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

module MAlonzo.Code.Matrix.Simple.Sum where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Matrix.Simple.Base

-- Matrix.Simple.Sum._.LeftIdentity
d_LeftIdentity_84 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftIdentity_84 = erased
-- Matrix.Simple.Sum._.RightIdentity
d_RightIdentity_114 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightIdentity_114 = erased
-- Matrix.Simple.Sum.identityˡ
d_identity'737'_152 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'737'_152 = erased
-- Matrix.Simple.Sum.identityʳ
d_identity'691'_154 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity'691'_154 = erased
-- Matrix.Simple.Sum.sum
d_sum_162 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  AgdaAny
d_sum_162 ~v0 v1 v2 ~v3 v4 v5 = du_sum_162 v1 v2 v4 v5
du_sum_162 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  AgdaAny
du_sum_162 v0 v1 v2 v3
  = case coe v2 of
      0 -> coe v1
      _ -> let v4 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                v0
                (coe
                   v3
                   (coe
                      MAlonzo.Code.Matrix.Simple.Base.C_ι_28
                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                (coe
                   du_sum_162 (coe v0) (coe v1) (coe v4)
                   (coe MAlonzo.Code.Matrix.Simple.Base.du_tail'8321'_108 (coe v3))))
-- Matrix.Simple.Sum.sum-nil
d_sum'45'nil_174 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45'nil_174 = erased
-- Matrix.Simple.Sum.sum-cong
d_sum'45'cong_184 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45'cong_184 = erased
-- Matrix.Simple.Sum.sum-reindex
d_sum'45'reindex_208 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45'reindex_208 = erased
-- Matrix.Simple.Sum.sum-zeros
d_sum'45'zeros_212 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45'zeros_212 = erased
-- Matrix.Simple.Sum.sum-distrib-tail₁
d_sum'45'distrib'45'tail'8321'_236 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45'distrib'45'tail'8321'_236 = erased
-- Matrix.Simple.Sum.split-sum
d_split'45'sum_254 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_split'45'sum_254 = erased
-- Matrix.Simple.Sum.expand-sum
d_expand'45'sum_296 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_expand'45'sum_296 = erased
-- Matrix.Simple.Sum.sum-swap
d_sum'45'swap_352 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45'swap_352 = erased
-- Matrix.Simple.Sum.sum-swap-helperˡ
d_sum'45'swap'45'helper'737'_364 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45'swap'45'helper'737'_364 = erased
-- Matrix.Simple.Sum.sum-swap-helperʳ
d_sum'45'swap'45'helper'691'_392 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45'swap'45'helper'691'_392 = erased
-- Matrix.Simple.Sum.merge-sum
d_merge'45'sum_514 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_merge'45'sum_514 = erased
-- Matrix.Simple.Sum.merge-sumₗ
d_merge'45'sum'8343'_520 ::
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_654 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_merge'45'sum'8343'_520 = erased
