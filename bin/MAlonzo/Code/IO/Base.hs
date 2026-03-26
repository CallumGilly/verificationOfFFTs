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

module MAlonzo.Code.IO.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Coinduction
import qualified MAlonzo.Code.Agda.Builtin.IO
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.IO.Primitive
import qualified MAlonzo.Code.Level

-- IO.Base.IO
d_IO_16 a0 a1 = ()
data T_IO_16
  = C_lift_22 (MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny) |
    C_pure_26 AgdaAny |
    C_bind_36 (MAlonzo.RTE.Infinity AgdaAny T_IO_16)
              (AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16) |
    C_seq_44 (MAlonzo.RTE.Infinity AgdaAny T_IO_16)
             (MAlonzo.RTE.Infinity AgdaAny T_IO_16)
-- IO.Base.lift!
d_lift'33'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_IO_16 -> T_IO_16
d_lift'33'_46 v0 ~v1 v2 v3 = du_lift'33'_46 v0 v2 v3
du_lift'33'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_IO_16 -> T_IO_16
du_lift'33'_46 v0 v1 v2
  = case coe v2 of
      C_lift_22 v3
        -> coe
             C_lift_22
             (coe
                MAlonzo.Code.IO.Primitive.d__'62''62''61'__12 v0 erased () erased
                v3
                (\ v4 ->
                   coe
                     MAlonzo.Code.IO.Primitive.d_pure_10 () erased
                     (coe MAlonzo.Code.Level.C_lift_20 (coe v4))))
      C_pure_26 v3
        -> coe C_pure_26 (coe MAlonzo.Code.Level.C_lift_20 (coe v3))
      C_bind_36 v4 v5
        -> coe
             C_bind_36 (coe du_'9839''45'0_1491 (coe v0) (coe v1) (coe v4))
             (coe du_'9839''45'1_1905 (coe v0) (coe v1) (coe v5))
      C_seq_44 v4 v5
        -> coe
             C_seq_44 (coe du_'9839''45'2_2729 (coe v0) (coe v1) (coe v4))
             (coe du_'9839''45'3_3133 (coe v0) (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- IO.Base._._<*>_
d__'60''42''62'__78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> T_IO_16 -> T_IO_16 -> T_IO_16
d__'60''42''62'__78 ~v0 ~v1 ~v2 v3 v4 = du__'60''42''62'__78 v3 v4
du__'60''42''62'__78 :: T_IO_16 -> T_IO_16 -> T_IO_16
du__'60''42''62'__78 v0 v1
  = coe
      C_bind_36 (coe du_'9839''45'4_5663 (coe v0))
      (coe du_'9839''45'5_5887 (coe v1))
-- IO.Base._._<$>_
d__'60''36''62'__88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> T_IO_16 -> T_IO_16
d__'60''36''62'__88 ~v0 ~v1 ~v2 v3 v4 = du__'60''36''62'__88 v3 v4
du__'60''36''62'__88 :: (AgdaAny -> AgdaAny) -> T_IO_16 -> T_IO_16
du__'60''36''62'__88 v0 v1
  = coe du__'60''42''62'__78 (coe C_pure_26 (coe v0)) (coe v1)
-- IO.Base._._<$_
d__'60''36'__94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> AgdaAny -> T_IO_16 -> T_IO_16
d__'60''36'__94 ~v0 ~v1 ~v2 v3 v4 = du__'60''36'__94 v3 v4
du__'60''36'__94 :: AgdaAny -> T_IO_16 -> T_IO_16
du__'60''36'__94 v0 v1
  = coe du__'60''36''62'__88 (coe (\ v2 -> v0)) (coe v1)
-- IO.Base._._>>=_
d__'62''62''61'__100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> T_IO_16 -> (AgdaAny -> T_IO_16) -> T_IO_16
d__'62''62''61'__100 ~v0 ~v1 ~v2 v3 v4
  = du__'62''62''61'__100 v3 v4
du__'62''62''61'__100 :: T_IO_16 -> (AgdaAny -> T_IO_16) -> T_IO_16
du__'62''62''61'__100 v0 v1
  = coe
      C_bind_36 (coe du_'9839''45'8_7581 (coe v0))
      (coe du_'9839''45'9_7805 (coe v1))
-- IO.Base._._=<<_
d__'61''60''60'__108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> T_IO_16) -> T_IO_16 -> T_IO_16
d__'61''60''60'__108 ~v0 ~v1 ~v2 v3 v4
  = du__'61''60''60'__108 v3 v4
du__'61''60''60'__108 :: (AgdaAny -> T_IO_16) -> T_IO_16 -> T_IO_16
du__'61''60''60'__108 v0 v1
  = coe du__'62''62''61'__100 (coe v1) (coe v0)
-- IO.Base._._>>_
d__'62''62'__110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> T_IO_16 -> T_IO_16 -> T_IO_16
d__'62''62'__110 ~v0 ~v1 ~v2 v3 v4 = du__'62''62'__110 v3 v4
du__'62''62'__110 :: T_IO_16 -> T_IO_16 -> T_IO_16
du__'62''62'__110 v0 v1
  = coe
      C_seq_44 (coe du_'9839''45'10_8543 (coe v0))
      (coe du_'9839''45'11_8757 (coe v1))
-- IO.Base._._<<_
d__'60''60'__116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> T_IO_16 -> T_IO_16 -> T_IO_16
d__'60''60'__116 ~v0 ~v1 ~v2 v3 v4 = du__'60''60'__116 v3 v4
du__'60''60'__116 :: T_IO_16 -> T_IO_16 -> T_IO_16
du__'60''60'__116 v0 v1 = coe du__'62''62'__110 (coe v1) (coe v0)
-- IO.Base.run
d_run_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_IO_16 -> MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny
d_run_118 v0 ~v1 v2 = du_run_118 v0 v2
du_run_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IO_16 -> MAlonzo.Code.Agda.Builtin.IO.T_IO_8 AgdaAny AgdaAny
du_run_118 v0 v1
  = case coe v1 of
      C_lift_22 v2 -> coe v2
      C_pure_26 v2
        -> coe MAlonzo.Code.IO.Primitive.d_pure_10 v0 erased v2
      C_bind_36 v3 v4
        -> coe
             MAlonzo.Code.IO.Primitive.d__'62''62''61'__12 v0 erased v0 erased
             (coe
                du_run_118 (coe v0)
                (coe MAlonzo.Code.Agda.Builtin.Coinduction.d_'9837'_22 (coe v3)))
             (\ v5 ->
                coe
                  du_run_118 (coe v0)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Coinduction.d_'9837'_22 (coe v4 v5)))
      C_seq_44 v3 v4
        -> coe
             MAlonzo.Code.IO.Primitive.d__'62''62''61'__12 v0 erased v0 erased
             (coe
                du_run_118 (coe v0)
                (coe MAlonzo.Code.Agda.Builtin.Coinduction.d_'9837'_22 (coe v3)))
             (\ v5 ->
                coe
                  du_run_118 (coe v0)
                  (coe MAlonzo.Code.Agda.Builtin.Coinduction.d_'9837'_22 (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- IO.Base.Main
d_Main_136 :: ()
d_Main_136 = erased
-- IO.Base.lift′
d_lift'8242'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    AgdaAny MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  T_IO_16
d_lift'8242'_138 v0 v1
  = coe
      C_lift_22
      (coe
         MAlonzo.Code.IO.Primitive.d__'62''62''61'__12 () erased v0 erased
         v1
         (\ v2 ->
            coe
              MAlonzo.Code.IO.Primitive.d_pure_10 v0 erased
              (coe
                 MAlonzo.Code.Level.C_lift_20
                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
-- IO.Base.ignore
d_ignore_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_IO_16 -> T_IO_16
d_ignore_144 ~v0 ~v1 v2 = du_ignore_144 v2
du_ignore_144 :: T_IO_16 -> T_IO_16
du_ignore_144 v0
  = coe
      du__'62''62'__110 (coe v0)
      (coe
         C_pure_26
         (coe
            MAlonzo.Code.Level.C_lift_20
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- IO.Base.when
d_when_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Bool -> T_IO_16 -> T_IO_16
d_when_148 ~v0 v1 v2 = du_when_148 v1 v2
du_when_148 :: Bool -> T_IO_16 -> T_IO_16
du_when_148 v0 v1
  = if coe v0
      then coe v1
      else coe
             C_pure_26
             (coe
                MAlonzo.Code.Level.C_lift_20
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- IO.Base.unless
d_unless_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Bool -> T_IO_16 -> T_IO_16
d_unless_152 ~v0 = du_unless_152
du_unless_152 :: Bool -> T_IO_16 -> T_IO_16
du_unless_152
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe du_when_148)
      (coe MAlonzo.Code.Data.Bool.Base.d_not_22)
-- IO.Base.whenJust
d_whenJust_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Maybe AgdaAny -> (AgdaAny -> T_IO_16) -> T_IO_16
d_whenJust_154 ~v0 ~v1 ~v2 v3 v4 = du_whenJust_154 v3 v4
du_whenJust_154 :: Maybe AgdaAny -> (AgdaAny -> T_IO_16) -> T_IO_16
du_whenJust_154 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v1 v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_pure_26
             (coe
                MAlonzo.Code.Level.C_lift_20
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- IO.Base.untilJust
d_untilJust_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> T_IO_16 -> T_IO_16
d_untilJust_160 v0 ~v1 v2 = du_untilJust_160 v0 v2
du_untilJust_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> T_IO_16 -> T_IO_16
du_untilJust_160 v0 v1
  = coe
      C_bind_36 (coe du_'9839''45'12_12351 (coe v1))
      (coe du_'46'extendedlambda0_164 (coe v0) (coe v1))
-- IO.Base..extendedlambda0
d_'46'extendedlambda0_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_IO_16 -> Maybe AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'46'extendedlambda0_164 v0 ~v1 v2 v3
  = du_'46'extendedlambda0_164 v0 v2 v3
du_'46'extendedlambda0_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IO_16 -> Maybe AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'46'extendedlambda0_164 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe du_'9839''45'14_12845 (coe v3)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_'9839''45'13_12573 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- IO.Base.untilRight
d_untilRight_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> T_IO_16) -> AgdaAny -> T_IO_16
d_untilRight_172 v0 ~v1 ~v2 v3 v4 = du_untilRight_172 v0 v3 v4
du_untilRight_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> T_IO_16) -> AgdaAny -> T_IO_16
du_untilRight_172 v0 v1 v2
  = coe
      C_bind_36 (coe du_'9839''45'15_13755 (coe v1) (coe v2))
      (coe du_'46'extendedlambda1_178 (coe v0) (coe v1))
-- IO.Base..extendedlambda1
d_'46'extendedlambda1_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> T_IO_16) ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'46'extendedlambda1_178 v0 ~v1 ~v2 v3 ~v4 v5
  = du_'46'extendedlambda1_178 v0 v3 v5
du_'46'extendedlambda1_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> T_IO_16) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'46'extendedlambda1_178 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> coe du_'9839''45'16_14145 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe du_'9839''45'17_14655 (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- IO.Base._.♯-0
d_'9839''45'0_1491 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  (AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16) ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'0_1491 v0 ~v1 v2 ~v3 v4 ~v5
  = du_'9839''45'0_1491 v0 v2 v4
du_'9839''45'0_1491 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'0_1491 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe
         du_lift'33'_46 (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d_'9837'_22 (coe v2)))
-- IO.Base._.♯-1
d_'9839''45'1_1905 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  (AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16) ->
  MAlonzo.Code.Level.T_Lift_8 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'1_1905 v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_'9839''45'1_1905 v0 v2 v5 v6
du_'9839''45'1_1905 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16) ->
  MAlonzo.Code.Level.T_Lift_8 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'1_1905 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe
         du_lift'33'_46 (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Coinduction.d_'9837'_22
            (coe v2 (MAlonzo.Code.Level.d_lower_18 (coe v3)))))
-- IO.Base._.♯-2
d_'9839''45'2_2729 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'2_2729 v0 ~v1 v2 ~v3 v4 ~v5
  = du_'9839''45'2_2729 v0 v2 v4
du_'9839''45'2_2729 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'2_2729 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe
         du_lift'33'_46 (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d_'9837'_22 (coe v2)))
-- IO.Base._.♯-3
d_'9839''45'3_3133 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'3_3133 v0 ~v1 v2 ~v3 ~v4 v5
  = du_'9839''45'3_3133 v0 v2 v5
du_'9839''45'3_3133 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16 ->
  MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'3_3133 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe
         du_lift'33'_46 (coe v0) (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Coinduction.d_'9837'_22 (coe v2)))
-- IO.Base._._.♯-4
d_'9839''45'4_5663 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> T_IO_16 -> T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'4_5663 ~v0 ~v1 ~v2 v3 ~v4 = du_'9839''45'4_5663 v3
du_'9839''45'4_5663 ::
  T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'4_5663 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16 (coe v0)
-- IO.Base._._.♯-5
d_'9839''45'5_5887 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T_IO_16 ->
  T_IO_16 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'5_5887 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'9839''45'5_5887 v4 v5
du_'9839''45'5_5887 ::
  T_IO_16 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'5_5887 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe
         C_bind_36 (coe du_'9839''45'6_6147 (coe v0))
         (coe du_'9839''45'7_6449 (coe v1)))
-- IO.Base._._._.♯-6
d_'9839''45'6_6147 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T_IO_16 ->
  T_IO_16 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'6_6147 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_'9839''45'6_6147 v4
du_'9839''45'6_6147 ::
  T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'6_6147 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16 (coe v0)
-- IO.Base._._._.♯-7
d_'9839''45'7_6449 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T_IO_16 ->
  T_IO_16 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'7_6449 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_'9839''45'7_6449 v5 v6
du_'9839''45'7_6449 ::
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'7_6449 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe C_pure_26 (coe v0 v1))
-- IO.Base._._.♯-8
d_'9839''45'8_7581 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T_IO_16 ->
  (AgdaAny -> T_IO_16) -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'8_7581 ~v0 ~v1 ~v2 v3 ~v4 = du_'9839''45'8_7581 v3
du_'9839''45'8_7581 ::
  T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'8_7581 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16 (coe v0)
-- IO.Base._._.♯-9
d_'9839''45'9_7805 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  T_IO_16 ->
  (AgdaAny -> T_IO_16) ->
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'9_7805 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'9839''45'9_7805 v4 v5
du_'9839''45'9_7805 ::
  (AgdaAny -> T_IO_16) ->
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'9_7805 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16 (coe v0 v1)
-- IO.Base._._.♯-10
d_'9839''45'10_8543 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> T_IO_16 -> T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'10_8543 ~v0 ~v1 ~v2 v3 ~v4 = du_'9839''45'10_8543 v3
du_'9839''45'10_8543 ::
  T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'10_8543 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16 (coe v0)
-- IO.Base._._.♯-11
d_'9839''45'11_8757 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> T_IO_16 -> T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'11_8757 ~v0 ~v1 ~v2 ~v3 v4 = du_'9839''45'11_8757 v4
du_'9839''45'11_8757 ::
  T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'11_8757 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16 (coe v0)
-- IO.Base._.♯-12
d_'9839''45'12_12351 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'12_12351 ~v0 ~v1 v2 = du_'9839''45'12_12351 v2
du_'9839''45'12_12351 ::
  T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'12_12351 v0
  = coe MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16 (coe v0)
-- IO.Base._.♯-13
d_'9839''45'13_12573 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'13_12573 v0 ~v1 v2 = du_'9839''45'13_12573 v0 v2
du_'9839''45'13_12573 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_IO_16 -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'13_12573 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe du_untilJust_160 (coe v0) (coe v1))
-- IO.Base._.♯-14
d_'9839''45'14_12845 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_IO_16 -> AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'14_12845 ~v0 ~v1 ~v2 v3 = du_'9839''45'14_12845 v3
du_'9839''45'14_12845 ::
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'14_12845 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe C_pure_26 (coe v0))
-- IO.Base._.♯-15
d_'9839''45'15_13755 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> T_IO_16) ->
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'15_13755 ~v0 ~v1 ~v2 v3 v4
  = du_'9839''45'15_13755 v3 v4
du_'9839''45'15_13755 ::
  (AgdaAny -> T_IO_16) ->
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'15_13755 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16 (coe v0 v1)
-- IO.Base._.♯-16
d_'9839''45'16_14145 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> T_IO_16) ->
  AgdaAny -> AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'16_14145 v0 ~v1 ~v2 v3 ~v4 v5
  = du_'9839''45'16_14145 v0 v3 v5
du_'9839''45'16_14145 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> T_IO_16) ->
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'16_14145 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe du_untilRight_172 (coe v0) (coe v1) (coe v2))
-- IO.Base._.♯-17
d_'9839''45'17_14655 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> T_IO_16) ->
  AgdaAny -> AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
d_'9839''45'17_14655 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'9839''45'17_14655 v5
du_'9839''45'17_14655 ::
  AgdaAny -> MAlonzo.RTE.Infinity AgdaAny T_IO_16
du_'9839''45'17_14655 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Coinduction.C_'9839'__16
      (coe C_pure_26 (coe v0))
