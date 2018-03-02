{-@
data User = User
	{ userEmail :: Text
	, userPassword :: Text Maybe
	, userVerkey :: Text Maybe
	, userVerified :: Bool
	}
@-}

{-@
data EntityField User typ where 
   Models.UserEmail :: EntityField User Text
 | Models.UserPassword :: EntityField User Text Maybe
 | Models.UserVerkey :: EntityField User Text Maybe
 | Models.UserVerified :: EntityField User Bool
 | Models.UserId :: EntityField User {v:_ | True}
@-}