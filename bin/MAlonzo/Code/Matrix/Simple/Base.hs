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

module MAlonzo.Code.Matrix.Simple.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base

-- Matrix.Simple.Base.Shape
d_Shape_16 = ()
data T_Shape_16
  = C_ι_18 Integer | C__'8855'__20 T_Shape_16 T_Shape_16
-- Matrix.Simple.Base.Position
d_Position_26 a0 = ()
data T_Position_26
  = C_ι_28 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C__'8855'__30 T_Position_26 T_Position_26
-- Matrix.Simple.Base.Ar
d_Ar_32 :: T_Shape_16 -> () -> ()
d_Ar_32 = erased
-- Matrix.Simple.Base.nil
d_nil_38 :: () -> T_Position_26 -> AgdaAny
d_nil_38 ~v0 ~v1 = du_nil_38
du_nil_38 :: AgdaAny
du_nil_38 = MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Base.ι-cons
d_ι'45'cons_40 ::
  () ->
  Integer ->
  AgdaAny -> (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
d_ι'45'cons_40 ~v0 ~v1 v2 v3 v4 = du_ι'45'cons_40 v2 v3 v4
du_ι'45'cons_40 ::
  AgdaAny -> (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
du_ι'45'cons_40 v0 v1 v2
  = case coe v2 of
      C_ι_28 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v0
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6 -> coe v1 (coe C_ι_28 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Base.length
d_length_52 :: T_Shape_16 -> Integer
d_length_52 v0
  = case coe v0 of
      C_ι_18 v1 -> coe v1
      C__'8855'__20 v1 v2
        -> coe mulInt (coe d_length_52 (coe v1)) (coe d_length_52 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Base.map
d_map_60 ::
  () ->
  () ->
  T_Shape_16 ->
  (AgdaAny -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
d_map_60 ~v0 ~v1 ~v2 v3 v4 v5 = du_map_60 v3 v4 v5
du_map_60 ::
  (AgdaAny -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
du_map_60 v0 v1 v2 = coe v0 (coe v1 v2)
-- Matrix.Simple.Base.imap
d_imap_68 ::
  T_Shape_16 ->
  () ->
  () ->
  (T_Position_26 -> AgdaAny -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
d_imap_68 ~v0 ~v1 ~v2 v3 v4 v5 = du_imap_68 v3 v4 v5
du_imap_68 ::
  (T_Position_26 -> AgdaAny -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
du_imap_68 v0 v1 v2 = coe v0 v2 (coe v1 v2)
-- Matrix.Simple.Base.nest
d_nest_76 ::
  T_Shape_16 ->
  T_Shape_16 ->
  () ->
  (T_Position_26 -> AgdaAny) ->
  T_Position_26 -> T_Position_26 -> AgdaAny
d_nest_76 ~v0 ~v1 ~v2 v3 v4 v5 = du_nest_76 v3 v4 v5
du_nest_76 ::
  (T_Position_26 -> AgdaAny) ->
  T_Position_26 -> T_Position_26 -> AgdaAny
du_nest_76 v0 v1 v2 = coe v0 (coe C__'8855'__30 v1 v2)
-- Matrix.Simple.Base.unnest
d_unnest_84 ::
  T_Shape_16 ->
  T_Shape_16 ->
  () ->
  (T_Position_26 -> T_Position_26 -> AgdaAny) ->
  T_Position_26 -> AgdaAny
d_unnest_84 ~v0 ~v1 ~v2 v3 v4 = du_unnest_84 v3 v4
du_unnest_84 ::
  (T_Position_26 -> T_Position_26 -> AgdaAny) ->
  T_Position_26 -> AgdaAny
du_unnest_84 v0 v1
  = case coe v1 of
      C__'8855'__30 v4 v5 -> coe v0 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Base.mapLeft
d_mapLeft_98 ::
  () ->
  () ->
  T_Shape_16 ->
  T_Shape_16 ->
  T_Shape_16 ->
  ((T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
d_mapLeft_98 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_mapLeft_98 v5 v6
du_mapLeft_98 ::
  ((T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
du_mapLeft_98 v0 v1
  = coe
      du_unnest_84 (coe du_map_60 (coe v0) (coe du_nest_76 (coe v1)))
-- Matrix.Simple.Base.head₁
d_head'8321'_104 ::
  Integer -> () -> (T_Position_26 -> AgdaAny) -> AgdaAny
d_head'8321'_104 ~v0 ~v1 v2 = du_head'8321'_104 v2
du_head'8321'_104 :: (T_Position_26 -> AgdaAny) -> AgdaAny
du_head'8321'_104 v0
  = coe v0 (coe C_ι_28 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Matrix.Simple.Base.tail₁
d_tail'8321'_108 ::
  Integer ->
  () -> (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
d_tail'8321'_108 ~v0 ~v1 v2 v3 = du_tail'8321'_108 v2 v3
du_tail'8321'_108 ::
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
du_tail'8321'_108 v0 v1
  = case coe v1 of
      C_ι_28 v3
        -> coe v0 (coe C_ι_28 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Base.splitArₗ
d_splitAr'8343'_114 ::
  Integer ->
  Integer ->
  () -> (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
d_splitAr'8343'_114 v0 ~v1 ~v2 v3 v4
  = du_splitAr'8343'_114 v0 v3 v4
du_splitAr'8343'_114 ::
  Integer -> (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
du_splitAr'8343'_114 v0 v1 v2
  = case coe v2 of
      C_ι_28 v4
        -> coe
             v1
             (coe
                C_ι_28
                (coe
                   MAlonzo.Code.Data.Fin.Base.du_join_166 v0
                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Base.splitArᵣ
d_splitAr'7523'_124 ::
  Integer ->
  Integer ->
  () -> (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
d_splitAr'7523'_124 v0 ~v1 ~v2 v3 v4
  = du_splitAr'7523'_124 v0 v3 v4
du_splitAr'7523'_124 ::
  Integer -> (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
du_splitAr'7523'_124 v0 v1 v2
  = case coe v2 of
      C_ι_28 v4
        -> coe
             v1
             (coe
                C_ι_28
                (coe
                   MAlonzo.Code.Data.Fin.Base.du_join_166 v0
                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Base.splitAr
d_splitAr_134 ::
  Integer ->
  Integer ->
  () ->
  (T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_splitAr_134 v0 ~v1 ~v2 v3 = du_splitAr_134 v0 v3
du_splitAr_134 ::
  Integer ->
  (T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_splitAr_134 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_splitAr'8343'_114 (coe v0) (coe v1))
      (coe du_splitAr'7523'_124 (coe v0) (coe v1))
-- Matrix.Simple.Base.foldr
d_foldr_144 ::
  Integer ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> (T_Position_26 -> AgdaAny) -> AgdaAny
d_foldr_144 v0 ~v1 ~v2 v3 v4 v5 = du_foldr_144 v0 v3 v4 v5
du_foldr_144 ::
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> (T_Position_26 -> AgdaAny) -> AgdaAny
du_foldr_144 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe v2
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_foldr_144 (coe v4) (coe v1)
                (coe v1 (coe du_head'8321'_104 (coe v3)) v2)
                (coe du_tail'8321'_108 (coe v3)))
-- Matrix.Simple.Base.zip
d_zip_160 ::
  Integer ->
  () ->
  () ->
  (T_Position_26 -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) ->
  T_Position_26 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zip_160 ~v0 ~v1 ~v2 v3 v4 v5 = du_zip_160 v3 v4 v5
du_zip_160 ::
  (T_Position_26 -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) ->
  T_Position_26 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zip_160 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v2) (coe v1 v2)
-- Matrix.Simple.Base.zipWith
d_zipWith_168 ::
  () ->
  () ->
  () ->
  T_Shape_16 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
d_zipWith_168 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_zipWith_168 v4 v5 v6 v7
du_zipWith_168 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) ->
  (T_Position_26 -> AgdaAny) -> T_Position_26 -> AgdaAny
du_zipWith_168 v0 v1 v2 v3 = coe v0 (coe v1 v3) (coe v2 v3)
-- Matrix.Simple.Base.iterate
d_iterate_180 ::
  () ->
  Integer ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_Position_26 -> AgdaAny
d_iterate_180 ~v0 v1 v2 v3 = du_iterate_180 v1 v2 v3
du_iterate_180 ::
  Integer ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_Position_26 -> AgdaAny
du_iterate_180 v0 v1 v2
  = case coe v0 of
      0 -> coe (\ v3 -> coe du_nil_38)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_ι'45'cons_40 (coe v2)
                (coe du_iterate_180 (coe v3) (coe v1) (coe v1 v2)))
