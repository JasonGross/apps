module R = Runtime.Main(struct
  include ExamplePwMgrWithSSBFull
  include ExamplePwMgrWithSSBFull.PwMgr
end);;

R.main ();;
