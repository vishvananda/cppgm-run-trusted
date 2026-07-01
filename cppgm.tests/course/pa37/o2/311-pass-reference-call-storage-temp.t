function @refload(%p : ptr [pass=reference]) -> ptr [prefer_local=yes] {
  block ^entry:
    %v = load ptr %p
    return ptr %v
}
function @main() -> ptr {
  block ^entry:
    %z = copy ptr nullptr
    %x = call ptr @refload(%z)
    return ptr %x
}
