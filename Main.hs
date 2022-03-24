
data IO a
    = Read Int (String -> IO a)
    | Write Int String (() -> IO a)



