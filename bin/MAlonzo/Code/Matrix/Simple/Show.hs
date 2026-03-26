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

module MAlonzo.Code.Matrix.Simple.Show where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Matrix.Simple.Base
import qualified MAlonzo.Code.Matrix.Simple.Reshape

-- Matrix.Simple.Show._++_
d__'43''43'__6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d__'43''43'__6
  = coe MAlonzo.Code.Agda.Builtin.String.d_primStringAppend_16
-- Matrix.Simple.Show.id
d_id_8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_id_8 v0 = coe v0
-- Matrix.Simple.Show.flipArr
d_flipArr_16 ::
  Integer ->
  () ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
d_flipArr_16 v0 ~v1 v2 v3 = du_flipArr_16 v0 v2 v3
du_flipArr_16 ::
  Integer ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny
du_flipArr_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_28 v4
        -> coe
             v1
             (coe
                MAlonzo.Code.Matrix.Simple.Base.C_ι_28
                (MAlonzo.Code.Data.Fin.Base.d_opposite_388 (coe v0) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Show.showShape
d_showShape_24 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showShape_24 v0
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v1
        -> coe
             d__'43''43'__6 ("\953 " :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v1 v2
        -> coe
             d__'43''43'__6 ("[" :: Data.Text.Text)
             (coe
                d__'43''43'__6 (d_showShape_24 (coe v1))
                (coe
                   d__'43''43'__6 ("] \8855 [" :: Data.Text.Text)
                   (coe
                      d__'43''43'__6 (d_showShape_24 (coe v2)) ("]" :: Data.Text.Text))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Show.show
d_show_36 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show_36 v0 ~v1 v2 v3 = du_show_36 v0 v2 v3
du_show_36 ::
  MAlonzo.Code.Matrix.Simple.Base.T_Shape_16 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_show_36 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Matrix.Simple.Base.C_ι_18 v3
        -> case coe v3 of
             0 -> coe
                    d__'43''43'__6 ("[" :: Data.Text.Text) ("]" :: Data.Text.Text)
             _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
                  coe
                    (coe
                       d__'43''43'__6
                       (coe
                          d__'43''43'__6 ("[" :: Data.Text.Text)
                          (coe
                             MAlonzo.Code.Matrix.Simple.Base.du_foldr_144 (coe v4)
                             (coe
                                (\ v5 v6 ->
                                   coe
                                     d__'43''43'__6 v6
                                     (coe
                                        d__'43''43'__6
                                        (coe
                                           d__'43''43'__6
                                           (coe
                                              d__'43''43'__6 (", " :: Data.Text.Text)
                                              ("(" :: Data.Text.Text))
                                           (coe v1 v5))
                                        (")" :: Data.Text.Text))))
                             (coe
                                d__'43''43'__6
                                (coe
                                   d__'43''43'__6 ("(" :: Data.Text.Text)
                                   (coe
                                      v1
                                      (coe
                                         MAlonzo.Code.Matrix.Simple.Base.du_head'8321'_104
                                         (coe v2))))
                                (")" :: Data.Text.Text))
                             (coe MAlonzo.Code.Matrix.Simple.Base.du_tail'8321'_108 (coe v2))))
                       ("]" :: Data.Text.Text))
      MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20 v3 v4
        -> coe
             du_show_36 (coe v3) (coe (\ v5 -> v5))
             (coe
                MAlonzo.Code.Matrix.Simple.Base.du_map_60
                (coe du_show_36 (coe v4) (coe v1))
                (coe MAlonzo.Code.Matrix.Simple.Base.du_nest_76 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Matrix.Simple.Show.showRow
d_showRow_66 ::
  () ->
  Integer ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showRow_66 ~v0 v1 v2 v3 = du_showRow_66 v1 v2 v3
du_showRow_66 ::
  Integer ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showRow_66 v0 v1 v2
  = case coe v0 of
      0 -> coe ("" :: Data.Text.Text)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Matrix.Simple.Base.du_foldr_144 (coe v3)
                (coe
                   (\ v4 v5 ->
                      coe
                        d__'43''43'__6 v5
                        (coe d__'43''43'__6 (", " :: Data.Text.Text) (coe v1 v4))))
                (coe
                   v1
                   (coe MAlonzo.Code.Matrix.Simple.Base.du_head'8321'_104 (coe v2)))
                (coe MAlonzo.Code.Matrix.Simple.Base.du_tail'8321'_108 (coe v2)))
-- Matrix.Simple.Show.showCSV
d_showCSV_82 ::
  () ->
  Integer ->
  Integer ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCSV_82 ~v0 v1 v2 v3 v4 v5 = du_showCSV_82 v1 v2 v3 v4 v5
du_showCSV_82 ::
  Integer ->
  Integer ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 ->
   MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  (MAlonzo.Code.Matrix.Simple.Base.T_Position_26 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showCSV_82 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Matrix.Simple.Base.du_foldr_144 (coe v1)
      (coe
         (\ v5 v6 ->
            coe
              d__'43''43'__6 v6
              (coe
                 d__'43''43'__6 (coe du_showRow_66 (coe v0) (coe v2) (coe v5))
                 ("\n" :: Data.Text.Text))))
      (coe
         d__'43''43'__6
         (coe du_showRow_66 (coe v0) (coe (\ v5 -> v5)) (coe v3))
         ("\n" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Matrix.Simple.Base.du_nest_76
         (coe
            MAlonzo.Code.Matrix.Simple.Reshape.du_reshape_88
            (coe
               MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
               (coe MAlonzo.Code.Matrix.Simple.Base.C_ι_18 (coe v0))
               (coe MAlonzo.Code.Matrix.Simple.Base.C_ι_18 (coe v1)))
            (coe
               MAlonzo.Code.Matrix.Simple.Base.C__'8855'__20
               (coe MAlonzo.Code.Matrix.Simple.Base.C_ι_18 (coe v1))
               (coe MAlonzo.Code.Matrix.Simple.Base.C_ι_18 (coe v0)))
            (coe MAlonzo.Code.Matrix.Simple.Reshape.C_swap_38) (coe v4)))
