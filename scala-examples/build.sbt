//scalaVersion := "0.20.0-RC1"
//scalaVersion := dottyLatestNightlyBuild.get
scalaVersion := "0.21.0-bin-20191209-0e761ea-NIGHTLY"

scalacOptions ++= Seq("-feature", "-deprecation")

scalaSource in Compile := baseDirectory.value
