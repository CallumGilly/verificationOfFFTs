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

module MAlonzo.Code.Matrix.Simple.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Matrix.Simple.Base

-- Matrix.Simple.Properties.tail₁-const
d_tail'8321''45'const_22 ::
  () ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tail'8321''45'const_22 = erased
-- Matrix.Simple.Properties.splitArᵣ-zero
d_splitAr'7523''45'zero_28 ::
  Integer ->
  () ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAr'7523''45'zero_28 = erased
-- Matrix.Simple.Properties.splitArₗ-zero
d_splitAr'8343''45'zero_36 ::
  Integer ->
  () ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_splitAr'8343''45'zero_36 = erased
-- Matrix.Simple.Properties.zipWith-congˡ
d_zipWith'45'cong'737'_48 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  () ->
  () ->
  () ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'cong'737'_48 = erased
-- Matrix.Simple.Properties.zipWith-congʳ
d_zipWith'45'cong'691'_64 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  () ->
  () ->
  () ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zipWith'45'cong'691'_64 = erased
-- Matrix.Simple.Properties.mapMap
d_mapMap_76 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mapMap_76 = erased
