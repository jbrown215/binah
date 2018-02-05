{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

{-@ LIQUID "--no-adt"                   @-}
{-@ LIQUID "--exact-data-con"           @-}
{-@ LIQUID "--higherorder"              @-}
{-@ LIQUID "--no-termination"           @-}

module Models where

import           Control.Monad
import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Persist.TH
import           Data.Aeson
import           Data.HashMap.Strict
import           Data.Int
import           Data.Map
import           Data.Proxy
import           Data.Text
import           Web.Internal.HttpApiData
import           Web.PathPieces

{-@ data EntityField Blob typ where
      Models.BlobXVal :: EntityField Blob {v:_ | v >= 10}
    | Models.BlobYVal :: EntityField Blob {v:_ | True}
    | Models.BlobId   :: EntityField Blob {v:_ | True}
  @-}

{-@ data Blob = Blob { blobXVal :: Int, blobYVal :: Int } @-}

{-@ assume Prelude.error :: String -> a @-} 

fieldError :: Text -> Text -> Text
fieldError fieldName err = "field " `mappend` fieldName `mappend` ": " `mappend` err

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft _ (Right r) = Right r
mapLeft f (Left l)  = Left (f l)

headNote :: [PersistValue] -> PersistValue
headNote (x:[]) = x
headNote xs = error $ "mkKeyFromValues: expected a list of one element, got: "
  `mappend` show xs

-- src/Models.hs:(25,1)-(37,2): Splicing declarations
instance PersistField Person where
  toPersistValue
    = \ ent_a8Fe
        -> (PersistMap
              $
                ((Prelude.zip ((Prelude.map Data.Text.pack) ["name", "age"]))
                   ((Prelude.map toPersistValue)
                      $
                        (toPersistFields ent_a8Fe))))
  fromPersistValue
    = ((\ x_a8Ff
          -> let columns_a8Fg = Data.HashMap.Strict.fromList x_a8Ff
             in
               (fromPersistValues
                  $
                    ((Prelude.map
                        (\ name_a8Fh
                           -> case
                                  (Data.HashMap.Strict.lookup (Data.Text.pack name_a8Fh)) columns_a8Fg
                              of
                                Just v_a8Fi -> v_a8Fi
                                Nothing -> PersistNull))
                       $ ["name", "age"])))
         <=<
           getPersistMap)
instance PersistFieldSql Person where
  sqlType _
    = SqlString
instance PersistField BlogPost where
  toPersistValue
    = \ ent_a8Fj
        -> (PersistMap
              $
                ((Prelude.zip
                    ((Prelude.map Data.Text.pack) ["title", "authorId"]))
                   ((Prelude.map toPersistValue)
                      $
                        (toPersistFields ent_a8Fj))))
  fromPersistValue
    = ((\ x_a8Fk
          -> let columns_a8Fl = Data.HashMap.Strict.fromList x_a8Fk
             in
               (fromPersistValues
                  $
                    ((Prelude.map
                        (\ name_a8Fm
                           -> case
                                  (Data.HashMap.Strict.lookup (Data.Text.pack name_a8Fm)) columns_a8Fl
                              of
                                Just v_a8Fn -> v_a8Fn
                                Nothing -> PersistNull))
                       $ ["title", "authorId"])))
         <=<
           getPersistMap)
instance PersistFieldSql BlogPost where
  sqlType _
    = SqlString
instance PersistField Blob where
  toPersistValue
    = \ ent_a8Fo
        -> (PersistMap
              $
                ((Prelude.zip ((Prelude.map Data.Text.pack) ["xVal", "yVal"]))
                   ((Prelude.map toPersistValue)
                      $
                        (toPersistFields ent_a8Fo))))
  fromPersistValue
    = ((\ x_a8Fp
          -> let columns_a8Fq = Data.HashMap.Strict.fromList x_a8Fp
             in
               (fromPersistValues
                  $
                    ((Prelude.map
                        (\ name_a8Fr
                           -> case
                                  (Data.HashMap.Strict.lookup (Data.Text.pack name_a8Fr)) columns_a8Fq
                              of
                                Just v_a8Fs -> v_a8Fs
                                Nothing -> PersistNull))
                       $ ["xVal", "yVal"])))
         <=<
           getPersistMap)
instance PersistFieldSql Blob where
  sqlType _
    = SqlString
data Person
  = Person {personName :: !String,
            personAge :: !(Maybe Int)}
  deriving Show
type PersonId = Key Person
instance PersistEntity Person where
  type PersistEntityBackend Person = SqlBackend
  data Unique Person
  newtype Key Person
    = PersonKey {unPersonKey :: (BackendKey SqlBackend)}
    deriving (Show,
              Read,
              Eq,
              Ord,
              Web.PathPieces.PathPiece,
              Web.Internal.HttpApiData.ToHttpApiData,
              Web.Internal.HttpApiData.FromHttpApiData,
              PersistField,
              PersistFieldSql,
              ToJSON,
              FromJSON)
  data EntityField Person typ
    = typ ~ Key Person =>
      PersonId |
      typ ~ String => PersonName |
      typ ~ Maybe Int => PersonAge
  keyToValues
    = ((: [])
         .
           (toPersistValue
              . unPersonKey))
  keyFromValues
    = ((fmap PersonKey)
         .
           (fromPersistValue
              . headNote))
  entityDef _
    = (((((((((EntityDef
                 (HaskellName
                    (Database.Persist.TH.packPTH "Person")))
                (DBName
                   (Database.Persist.TH.packPTH "person")))
               (((((((FieldDef
                        (HaskellName
                           (Database.Persist.TH.packPTH "Id")))
                       (DBName
                          (Database.Persist.TH.packPTH "id")))
                      ((FTTypeCon Nothing)
                         (Database.Persist.TH.packPTH "PersonId")))
                     SqlInt64)
                    [])
                   True)
                  ((ForeignRef
                      (HaskellName
                         (Database.Persist.TH.packPTH "Person")))
                     ((FTTypeCon
                         (Just (Database.Persist.TH.packPTH "Data.Int")))
                        (Database.Persist.TH.packPTH "Int64")))))
              [])
             [((((((FieldDef
                      (HaskellName
                         (Database.Persist.TH.packPTH "name")))
                     (DBName
                        (Database.Persist.TH.packPTH "name")))
                    ((FTTypeCon Nothing)
                       (Database.Persist.TH.packPTH "String")))
                   SqlString)
                  [])
                 True)
                NoReference,
              ((((((FieldDef
                      (HaskellName
                         (Database.Persist.TH.packPTH "age")))
                     (DBName
                        (Database.Persist.TH.packPTH "age")))
                    ((FTTypeCon Nothing)
                       (Database.Persist.TH.packPTH "Int")))
                   SqlInt64)
                  [Database.Persist.TH.packPTH "Maybe"])
                 True)
                NoReference])
            [])
           [])
          [Database.Persist.TH.packPTH "Show"])
         (Data.Map.fromList []))
        False
  toPersistFields
    (Person x_a8Ft x_a8Fu)
    = [SomePersistField x_a8Ft,
       SomePersistField x_a8Fu]
  fromPersistValues
    [x1_a8Fw, x2_a8Fx]
    = Person
        <$>
          ((mapLeft
              (fieldError
                 (Database.Persist.TH.packPTH "name")))
             . fromPersistValue)
            x1_a8Fw
        <*>
          ((mapLeft
              (fieldError
                 (Database.Persist.TH.packPTH "age")))
             . fromPersistValue)
            x2_a8Fx
  fromPersistValues x_a8Fv
    = (Left
         $
           ((mappend
               (Database.Persist.TH.packPTH
                  "Person: fromPersistValues failed on: "))
              (Data.Text.pack $ (show x_a8Fv))))
  persistUniqueToFieldNames _
    = error "Degenerate case, should never happen"
  persistUniqueToValues _
    = error "Degenerate case, should never happen"
  persistUniqueKeys
    (Person _name_a8Fy _age_a8Fz)
    = []
  persistFieldDef PersonId
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "Id")))
             (DBName
                (Database.Persist.TH.packPTH "id")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "PersonId")))
           SqlInt64)
          [])
         True)
        ((ForeignRef
            (HaskellName
               (Database.Persist.TH.packPTH "Person")))
           ((FTTypeCon
               (Just (Database.Persist.TH.packPTH "Data.Int")))
              (Database.Persist.TH.packPTH "Int64")))
  persistFieldDef PersonName
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "name")))
             (DBName
                (Database.Persist.TH.packPTH "name")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "String")))
           SqlString)
          [])
         True)
        NoReference
  persistFieldDef PersonAge
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "age")))
             (DBName
                (Database.Persist.TH.packPTH "age")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "Int")))
           SqlInt64)
          [Database.Persist.TH.packPTH "Maybe"])
         True)
        NoReference
  persistIdField = PersonId
  fieldLens PersonId
    = (Database.Persist.TH.lensPTH
         entityKey)
        (\ (Entity _ value_a8FA)
           key_a8FB
           -> (Entity key_a8FB)
                value_a8FA)
  fieldLens PersonName
    = (Database.Persist.TH.lensPTH
         (personName
            . entityVal))
        (\ (Entity key_a8FC value_a8FD)
           x_a8FE
           -> (Entity key_a8FC)
                value_a8FD {personName = x_a8FE})
  fieldLens PersonAge
    = (Database.Persist.TH.lensPTH
         (personAge
            . entityVal))
        (\ (Entity key_a8FC value_a8FD)
           x_a8FE
           -> (Entity key_a8FC)
                value_a8FD {personAge = x_a8FE})
instance ToBackendKey SqlBackend Person where
  toBackendKey = unPersonKey
  fromBackendKey = PersonKey
data BlogPost
  = BlogPost {blogPostTitle :: !String,
              blogPostAuthorId :: !(Key Person)}
  deriving Show
type BlogPostId = Key BlogPost
instance PersistEntity BlogPost where
  type PersistEntityBackend BlogPost = SqlBackend
  data Unique BlogPost
  newtype Key BlogPost
    = BlogPostKey {unBlogPostKey :: (BackendKey SqlBackend)}
    deriving (Show,
              Read,
              Eq,
              Ord,
              Web.PathPieces.PathPiece,
              Web.Internal.HttpApiData.ToHttpApiData,
              Web.Internal.HttpApiData.FromHttpApiData,
              PersistField,
              PersistFieldSql,
              ToJSON,
              FromJSON)
  data EntityField BlogPost typ
    = typ ~ Key BlogPost =>
      BlogPostId |
      typ ~ String => BlogPostTitle |
      typ ~ Key Person =>
      BlogPostAuthorId
  keyToValues
    = ((: [])
         .
           (toPersistValue
              . unBlogPostKey))
  keyFromValues
    = ((fmap BlogPostKey)
         .
           (fromPersistValue
              . headNote))
  entityDef _
    = (((((((((EntityDef
                 (HaskellName
                    (Database.Persist.TH.packPTH "BlogPost")))
                (DBName
                   (Database.Persist.TH.packPTH "blog_post")))
               (((((((FieldDef
                        (HaskellName
                           (Database.Persist.TH.packPTH "Id")))
                       (DBName
                          (Database.Persist.TH.packPTH "id")))
                      ((FTTypeCon Nothing)
                         (Database.Persist.TH.packPTH "BlogPostId")))
                     SqlInt64)
                    [])
                   True)
                  ((ForeignRef
                      (HaskellName
                         (Database.Persist.TH.packPTH "BlogPost")))
                     ((FTTypeCon
                         (Just (Database.Persist.TH.packPTH "Data.Int")))
                        (Database.Persist.TH.packPTH "Int64")))))
              [])
             [((((((FieldDef
                      (HaskellName
                         (Database.Persist.TH.packPTH "title")))
                     (DBName
                        (Database.Persist.TH.packPTH "title")))
                    ((FTTypeCon Nothing)
                       (Database.Persist.TH.packPTH "String")))
                   SqlString)
                  [])
                 True)
                NoReference,
              ((((((FieldDef
                      (HaskellName
                         (Database.Persist.TH.packPTH "authorId")))
                     (DBName
                        (Database.Persist.TH.packPTH "author_id")))
                    ((FTTypeCon Nothing)
                       (Database.Persist.TH.packPTH "PersonId")))
                   (sqlType
                      (Data.Proxy.Proxy :: Data.Proxy.Proxy Int64)))
                  [])
                 True)
                ((ForeignRef
                    (HaskellName
                       (Database.Persist.TH.packPTH "Person")))
                   ((FTTypeCon
                       (Just (Database.Persist.TH.packPTH "Data.Int")))
                      (Database.Persist.TH.packPTH "Int64")))])
            [])
           [])
          [Database.Persist.TH.packPTH "Show"])
         (Data.Map.fromList []))
        False
  toPersistFields
    (BlogPost x_a8FF x_a8FG)
    = [SomePersistField x_a8FF,
       SomePersistField x_a8FG]
  fromPersistValues
    [x1_a8FI, x2_a8FJ]
    = BlogPost
        <$>
          ((mapLeft
              (fieldError
                 (Database.Persist.TH.packPTH "title")))
             . fromPersistValue)
            x1_a8FI
        <*>
          ((mapLeft
              (fieldError
                 (Database.Persist.TH.packPTH "authorId")))
             . fromPersistValue)
            x2_a8FJ
  fromPersistValues x_a8FH
    = (Left
         $
           ((mappend
               (Database.Persist.TH.packPTH
                  "BlogPost: fromPersistValues failed on: "))
              (Data.Text.pack $ (show x_a8FH))))
  persistUniqueToFieldNames _
    = error "Degenerate case, should never happen"
  persistUniqueToValues _
    = error "Degenerate case, should never happen"
  persistUniqueKeys
    (BlogPost _title_a8FK _authorId_a8FL)
    = []
  persistFieldDef BlogPostId
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "Id")))
             (DBName
                (Database.Persist.TH.packPTH "id")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "BlogPostId")))
           SqlInt64)
          [])
         True)
        ((ForeignRef
            (HaskellName
               (Database.Persist.TH.packPTH "BlogPost")))
           ((FTTypeCon
               (Just (Database.Persist.TH.packPTH "Data.Int")))
              (Database.Persist.TH.packPTH "Int64")))
  persistFieldDef BlogPostTitle
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "title")))
             (DBName
                (Database.Persist.TH.packPTH "title")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "String")))
           SqlString)
          [])
         True)
        NoReference
  persistFieldDef
    BlogPostAuthorId
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "authorId")))
             (DBName
                (Database.Persist.TH.packPTH "author_id")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "PersonId")))
           SqlInt64)
          [])
         True)
        ((ForeignRef
            (HaskellName
               (Database.Persist.TH.packPTH "Person")))
           ((FTTypeCon
               (Just (Database.Persist.TH.packPTH "Data.Int")))
              (Database.Persist.TH.packPTH "Int64")))
  persistIdField = BlogPostId
  fieldLens BlogPostId
    = (Database.Persist.TH.lensPTH
         entityKey)
        (\ (Entity _ value_a8FM)
           key_a8FN
           -> (Entity key_a8FN)
                value_a8FM)
  fieldLens BlogPostTitle
    = (Database.Persist.TH.lensPTH
         (blogPostTitle
            . entityVal))
        (\ (Entity key_a8FO value_a8FP)
           x_a8FQ
           -> (Entity key_a8FO)
                value_a8FP {blogPostTitle = x_a8FQ})
  fieldLens BlogPostAuthorId
    = (Database.Persist.TH.lensPTH
         (blogPostAuthorId
            . entityVal))
        (\ (Entity key_a8FO value_a8FP)
           x_a8FQ
           -> (Entity key_a8FO)
                value_a8FP {blogPostAuthorId = x_a8FQ})
instance ToBackendKey SqlBackend BlogPost where
  toBackendKey = unBlogPostKey
  fromBackendKey = BlogPostKey
data Blob
  = Blob {blobXVal :: Int, blobYVal :: Int}
  deriving ()
type BlobId = Key Blob
instance PersistEntity Blob where
  type PersistEntityBackend Blob = SqlBackend
  data Unique Blob
  newtype Key Blob
    = BlobKey {unBlobKey :: (BackendKey SqlBackend)}
    deriving (Show,
              Read,
              Eq,
              Ord,
              Web.PathPieces.PathPiece,
              Web.Internal.HttpApiData.ToHttpApiData,
              Web.Internal.HttpApiData.FromHttpApiData,
              PersistField,
              PersistFieldSql,
              ToJSON,
              FromJSON)
  data EntityField Blob typ
    = typ ~ Key Blob => BlobId |
      typ ~ Int => BlobXVal |
      typ ~ Int => BlobYVal
  keyToValues
    = ((: [])
         .
           (toPersistValue
              . unBlobKey))
  keyFromValues
    = ((fmap BlobKey)
         .
           (fromPersistValue
              . headNote))
  entityDef _
    = (((((((((EntityDef
                 (HaskellName
                    (Database.Persist.TH.packPTH "Blob")))
                (DBName
                   (Database.Persist.TH.packPTH "blob")))
               (((((((FieldDef
                        (HaskellName
                           (Database.Persist.TH.packPTH "Id")))
                       (DBName
                          (Database.Persist.TH.packPTH "id")))
                      ((FTTypeCon Nothing)
                         (Database.Persist.TH.packPTH "BlobId")))
                     SqlInt64)
                    [])
                   True)
                  ((ForeignRef
                      (HaskellName
                         (Database.Persist.TH.packPTH "Blob")))
                     ((FTTypeCon
                         (Just (Database.Persist.TH.packPTH "Data.Int")))
                        (Database.Persist.TH.packPTH "Int64")))))
              [])
             [((((((FieldDef
                      (HaskellName
                         (Database.Persist.TH.packPTH "xVal")))
                     (DBName
                        (Database.Persist.TH.packPTH "x_val")))
                    ((FTTypeCon Nothing)
                       (Database.Persist.TH.packPTH "Int")))
                   SqlInt64)
                  [])
                 False)
                NoReference,
              ((((((FieldDef
                      (HaskellName
                         (Database.Persist.TH.packPTH "yVal")))
                     (DBName
                        (Database.Persist.TH.packPTH "y_val")))
                    ((FTTypeCon Nothing)
                       (Database.Persist.TH.packPTH "Int")))
                   SqlInt64)
                  [])
                 False)
                NoReference])
            [])
           [])
          [])
         (Data.Map.fromList []))
        False
  toPersistFields
    (Blob x_a8FR x_a8FS)
    = [SomePersistField x_a8FR,
       SomePersistField x_a8FS]
  fromPersistValues
    [x1_a8FU, x2_a8FV]
    = Blob
        <$>
          ((mapLeft
              (fieldError
                 (Database.Persist.TH.packPTH "xVal")))
             . fromPersistValue)
            x1_a8FU
        <*>
          ((mapLeft
              (fieldError
                 (Database.Persist.TH.packPTH "yVal")))
             . fromPersistValue)
            x2_a8FV
  fromPersistValues x_a8FT
    = (Left
         $
           ((mappend
               (Database.Persist.TH.packPTH
                  "Blob: fromPersistValues failed on: "))
              (Data.Text.pack $ (show x_a8FT))))
  persistUniqueToFieldNames _
    = error "Degenerate case, should never happen"
  persistUniqueToValues _
    = error "Degenerate case, should never happen"
  persistUniqueKeys
    (Blob _xVal_a8FW _yVal_a8FX)
    = []
  persistFieldDef BlobId
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "Id")))
             (DBName
                (Database.Persist.TH.packPTH "id")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "BlobId")))
           SqlInt64)
          [])
         True)
        ((ForeignRef
            (HaskellName
               (Database.Persist.TH.packPTH "Blob")))
           ((FTTypeCon
               (Just (Database.Persist.TH.packPTH "Data.Int")))
              (Database.Persist.TH.packPTH "Int64")))
  persistFieldDef BlobXVal
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "xVal")))
             (DBName
                (Database.Persist.TH.packPTH "x_val")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "Int")))
           SqlInt64)
          [])
         False)
        NoReference
  persistFieldDef BlobYVal
    = ((((((FieldDef
              (HaskellName
                 (Database.Persist.TH.packPTH "yVal")))
             (DBName
                (Database.Persist.TH.packPTH "y_val")))
            ((FTTypeCon Nothing)
               (Database.Persist.TH.packPTH "Int")))
           SqlInt64)
          [])
         False)
        NoReference
  persistIdField = BlobId
  fieldLens BlobId
    = (Database.Persist.TH.lensPTH
         entityKey)
        (\ (Entity _ value_a8FY)
           key_a8FZ
           -> (Entity key_a8FZ)
                value_a8FY)
  fieldLens BlobXVal
    = (Database.Persist.TH.lensPTH
         (blobXVal
            . entityVal))
        (\ (Entity key_a8G0 value_a8G1)
           x_a8G2
           -> (Entity key_a8G0)
                value_a8G1 {blobXVal = x_a8G2})
  fieldLens BlobYVal
    = (Database.Persist.TH.lensPTH
         (blobYVal
            . entityVal))
        (\ (Entity key_a8G0 value_a8G1)
           x_a8G2
           -> (Entity key_a8G0)
                value_a8G1 {blobYVal = x_a8G2})
instance ToBackendKey SqlBackend Blob where
  toBackendKey = unBlobKey
  fromBackendKey = BlobKey
migrateAll :: Migration
migrateAll
  = do let defs_a8G3
             = [(((((((((EntityDef
                           (HaskellName
                              (Database.Persist.TH.packPTH "Person")))
                          (DBName
                             (Database.Persist.TH.packPTH "person")))
                         (((((((FieldDef
                                  (HaskellName
                                     (Database.Persist.TH.packPTH "Id")))
                                 (DBName
                                    (Database.Persist.TH.packPTH "id")))
                                ((FTTypeCon Nothing)
                                   (Database.Persist.TH.packPTH "PersonId")))
                               SqlInt64)
                              [])
                             True)
                            ((ForeignRef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "Person")))
                               ((FTTypeCon
                                   (Just (Database.Persist.TH.packPTH "Data.Int")))
                                  (Database.Persist.TH.packPTH "Int64")))))
                        [])
                       [((((((FieldDef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "name")))
                               (DBName
                                  (Database.Persist.TH.packPTH "name")))
                              ((FTTypeCon Nothing)
                                 (Database.Persist.TH.packPTH "String")))
                             SqlString)
                            [])
                           True)
                          NoReference,
                        ((((((FieldDef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "age")))
                               (DBName
                                  (Database.Persist.TH.packPTH "age")))
                              ((FTTypeCon Nothing)
                                 (Database.Persist.TH.packPTH "Int")))
                             SqlInt64)
                            [Database.Persist.TH.packPTH "Maybe"])
                           True)
                          NoReference])
                      [])
                     [])
                    [Database.Persist.TH.packPTH "Show"])
                   (Data.Map.fromList []))
                  False,
                (((((((((EntityDef
                           (HaskellName
                              (Database.Persist.TH.packPTH "BlogPost")))
                          (DBName
                             (Database.Persist.TH.packPTH "blog_post")))
                         (((((((FieldDef
                                  (HaskellName
                                     (Database.Persist.TH.packPTH "Id")))
                                 (DBName
                                    (Database.Persist.TH.packPTH "id")))
                                ((FTTypeCon Nothing)
                                   (Database.Persist.TH.packPTH "BlogPostId")))
                               SqlInt64)
                              [])
                             True)
                            ((ForeignRef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "BlogPost")))
                               ((FTTypeCon
                                   (Just (Database.Persist.TH.packPTH "Data.Int")))
                                  (Database.Persist.TH.packPTH "Int64")))))
                        [])
                       [((((((FieldDef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "title")))
                               (DBName
                                  (Database.Persist.TH.packPTH "title")))
                              ((FTTypeCon Nothing)
                                 (Database.Persist.TH.packPTH "String")))
                             SqlString)
                            [])
                           True)
                          NoReference,
                        ((((((FieldDef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "authorId")))
                               (DBName
                                  (Database.Persist.TH.packPTH "author_id")))
                              ((FTTypeCon Nothing)
                                 (Database.Persist.TH.packPTH "PersonId")))
                             (sqlType
                                (Data.Proxy.Proxy :: Data.Proxy.Proxy Int64)))
                            [])
                           True)
                          ((ForeignRef
                              (HaskellName
                                 (Database.Persist.TH.packPTH "Person")))
                             ((FTTypeCon
                                 (Just (Database.Persist.TH.packPTH "Data.Int")))
                                (Database.Persist.TH.packPTH "Int64")))])
                      [])
                     [])
                    [Database.Persist.TH.packPTH "Show"])
                   (Data.Map.fromList []))
                  False,
                (((((((((EntityDef
                           (HaskellName
                              (Database.Persist.TH.packPTH "Blob")))
                          (DBName
                             (Database.Persist.TH.packPTH "blob")))
                         (((((((FieldDef
                                  (HaskellName
                                     (Database.Persist.TH.packPTH "Id")))
                                 (DBName
                                    (Database.Persist.TH.packPTH "id")))
                                ((FTTypeCon Nothing)
                                   (Database.Persist.TH.packPTH "BlobId")))
                               SqlInt64)
                              [])
                             True)
                            ((ForeignRef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "Blob")))
                               ((FTTypeCon
                                   (Just (Database.Persist.TH.packPTH "Data.Int")))
                                  (Database.Persist.TH.packPTH "Int64")))))
                        [])
                       [((((((FieldDef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "xVal")))
                               (DBName
                                  (Database.Persist.TH.packPTH "x_val")))
                              ((FTTypeCon Nothing)
                                 (Database.Persist.TH.packPTH "Int")))
                             SqlInt64)
                            [])
                           False)
                          NoReference,
                        ((((((FieldDef
                                (HaskellName
                                   (Database.Persist.TH.packPTH "yVal")))
                               (DBName
                                  (Database.Persist.TH.packPTH "y_val")))
                              ((FTTypeCon Nothing)
                                 (Database.Persist.TH.packPTH "Int")))
                             SqlInt64)
                            [])
                           False)
                          NoReference])
                      [])
                     [])
                    [])
                   (Data.Map.fromList []))
                  False]
       (migrate defs_a8G3)
         ((((((((((EntityDef
                     (HaskellName
                        (Database.Persist.TH.packPTH "Person")))
                    (DBName
                       (Database.Persist.TH.packPTH "person")))
                   (((((((FieldDef
                            (HaskellName
                               (Database.Persist.TH.packPTH "Id")))
                           (DBName
                              (Database.Persist.TH.packPTH "id")))
                          ((FTTypeCon Nothing)
                             (Database.Persist.TH.packPTH "PersonId")))
                         SqlInt64)
                        [])
                       True)
                      ((ForeignRef
                          (HaskellName
                             (Database.Persist.TH.packPTH "Person")))
                         ((FTTypeCon
                             (Just (Database.Persist.TH.packPTH "Data.Int")))
                            (Database.Persist.TH.packPTH "Int64")))))
                  [])
                 [((((((FieldDef
                          (HaskellName
                             (Database.Persist.TH.packPTH "name")))
                         (DBName
                            (Database.Persist.TH.packPTH "name")))
                        ((FTTypeCon Nothing)
                           (Database.Persist.TH.packPTH "String")))
                       SqlString)
                      [])
                     True)
                    NoReference,
                  ((((((FieldDef
                          (HaskellName
                             (Database.Persist.TH.packPTH "age")))
                         (DBName
                            (Database.Persist.TH.packPTH "age")))
                        ((FTTypeCon Nothing)
                           (Database.Persist.TH.packPTH "Int")))
                       SqlInt64)
                      [Database.Persist.TH.packPTH "Maybe"])
                     True)
                    NoReference])
                [])
               [])
              [Database.Persist.TH.packPTH "Show"])
             (Data.Map.fromList []))
            False)
       (migrate defs_a8G3)
         ((((((((((EntityDef
                     (HaskellName
                        (Database.Persist.TH.packPTH "BlogPost")))
                    (DBName
                       (Database.Persist.TH.packPTH "blog_post")))
                   (((((((FieldDef
                            (HaskellName
                               (Database.Persist.TH.packPTH "Id")))
                           (DBName
                              (Database.Persist.TH.packPTH "id")))
                          ((FTTypeCon Nothing)
                             (Database.Persist.TH.packPTH "BlogPostId")))
                         SqlInt64)
                        [])
                       True)
                      ((ForeignRef
                          (HaskellName
                             (Database.Persist.TH.packPTH "BlogPost")))
                         ((FTTypeCon
                             (Just (Database.Persist.TH.packPTH "Data.Int")))
                            (Database.Persist.TH.packPTH "Int64")))))
                  [])
                 [((((((FieldDef
                          (HaskellName
                             (Database.Persist.TH.packPTH "title")))
                         (DBName
                            (Database.Persist.TH.packPTH "title")))
                        ((FTTypeCon Nothing)
                           (Database.Persist.TH.packPTH "String")))
                       SqlString)
                      [])
                     True)
                    NoReference,
                  ((((((FieldDef
                          (HaskellName
                             (Database.Persist.TH.packPTH "authorId")))
                         (DBName
                            (Database.Persist.TH.packPTH "author_id")))
                        ((FTTypeCon Nothing)
                           (Database.Persist.TH.packPTH "PersonId")))
                       (sqlType
                          (Data.Proxy.Proxy :: Data.Proxy.Proxy Int64)))
                      [])
                     True)
                    ((ForeignRef
                        (HaskellName
                           (Database.Persist.TH.packPTH "Person")))
                       ((FTTypeCon
                           (Just (Database.Persist.TH.packPTH "Data.Int")))
                          (Database.Persist.TH.packPTH "Int64")))])
                [])
               [])
              [Database.Persist.TH.packPTH "Show"])
             (Data.Map.fromList []))
            False)
       (migrate defs_a8G3)
         ((((((((((EntityDef
                     (HaskellName
                        (Database.Persist.TH.packPTH "Blob")))
                    (DBName
                       (Database.Persist.TH.packPTH "blob")))
                   (((((((FieldDef
                            (HaskellName
                               (Database.Persist.TH.packPTH "Id")))
                           (DBName
                              (Database.Persist.TH.packPTH "id")))
                          ((FTTypeCon Nothing)
                             (Database.Persist.TH.packPTH "BlobId")))
                         SqlInt64)
                        [])
                       True)
                      ((ForeignRef
                          (HaskellName
                             (Database.Persist.TH.packPTH "Blob")))
                         ((FTTypeCon
                             (Just (Database.Persist.TH.packPTH "Data.Int")))
                            (Database.Persist.TH.packPTH "Int64")))))
                  [])
                 [((((((FieldDef
                          (HaskellName
                             (Database.Persist.TH.packPTH "xVal")))
                         (DBName
                            (Database.Persist.TH.packPTH "x_val")))
                        ((FTTypeCon Nothing)
                           (Database.Persist.TH.packPTH "Int")))
                       SqlInt64)
                      [])
                     False)
                    NoReference,
                  ((((((FieldDef
                          (HaskellName
                             (Database.Persist.TH.packPTH "yVal")))
                         (DBName
                            (Database.Persist.TH.packPTH "y_val")))
                        ((FTTypeCon Nothing)
                           (Database.Persist.TH.packPTH "Int")))
                       SqlInt64)
                      [])
                     False)
                    NoReference])
                [])
               [])
              [])
             (Data.Map.fromList []))
            False)
