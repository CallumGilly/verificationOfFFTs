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

module MAlonzo.Code.Matrix.Simple.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Matrix.Simple.Base

-- Matrix.Simple.Equality._≅_
d__'8773'__16 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  () ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) -> ()
d__'8773'__16 = erased
-- Matrix.Simple.Equality.reduce-≅
d_reduce'45''8773'_30 ::
  Integer ->
  () ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduce'45''8773'_30 = erased
-- Matrix.Simple.Equality.tail₁-cong
d_tail'8321''45'cong_52 ::
  Integer ->
  () ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tail'8321''45'cong_52 = erased
