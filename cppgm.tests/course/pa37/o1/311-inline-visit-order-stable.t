function @zcaller(%x : i64) -> i64 {
  block ^entry:
    %v = call i64 @mcallee(%x)
    return i64 %v
}

function @mcallee(%x : i64) -> i64 [prefer_local=yes] {
  block ^entry:
    %v = call i64 @aleaf(%x)
    %w = binary mul i64 %v, 2
    return i64 %w
}

function @aleaf(%x : i64) -> i64 [prefer_local=yes] {
  block ^entry:
    %v = binary add i64 %x, 1
    return i64 %v
}
