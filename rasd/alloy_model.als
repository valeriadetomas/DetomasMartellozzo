
sig Username{}
sig Password{}
{
 all p: Password | ( some u: User |  u.password  = p)
}
sig Surname{}
sig Email{}
sig Code{}

abstract sig User{
	password: one Password
}

sig Farmer extends User{
    username: one Username,
    surname: one Surname,
    email: one Email
}

sig PolicyMaker extends User{
    code: one Code 
}
    

sig Date{
    day: one Int,
    month: one Int,
    year: one Int
}{
    day > 0
    month > 0
    year > 0
}

sig Time{
    hour : one Int,
    minute : one Int
}{
    hour > 0
    minute >= 0
}
sig MessageContent{}

sig Message{
    date: one Date,
    time: one Time,
    content: one MessageContent,
    sender: one Farmer
}

one sig Forum{
    messages: set Message
}

sig ProductName{}

sig Product{
    name: one ProductName
}

sig Production{
    type: one Product,
    amount: one Int,
    date : one Date
}{
	amount > 0
}

sig SensorData{
    quantity: Int, 
    date: Date
}{
	quantity >= 0
}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Notification{
    body: one MessageContent,
    typeOfProduction: one Production,
    date: one Date,
    time: one Time 
}

sig Help extends Notification{
    sender: one Farmer,
    receiver: one PolicyMaker
}
sig Advice extends Notification{
    sender: one Farmer,
    receiver: one PolicyMaker
}

sig Solution extends Notification{
    sender: one PolicyMaker,
    receiver: one Farmer
}

sig Evaluation extends Notification{
    sender: one PolicyMaker,
    receiver: one Farmer,
    result: one Bool
}

sig Position {}
sig Weather{}

sig WeatherInfo{
    basicInfo: Weather,
    temperature: Int,
    position: one Position,
    date: Date
}

sig FarmName{}

sig Farm{
    name: one FarmName,
    owner: one Farmer,
    products: set Production,
    water: some SensorData,
    humidity: some SensorData,
    position: one Position, 
    weather: some WeatherInfo, 
    evaluation: set Evaluation
}

one sig Map{
    farms: some Farm
}


//Bool can only be true or false
fact boolean{
    True + False = Bool
}

//Uniquness of farmer's username and email
fact UniqueUsernames{
    no disj f1,f2: Farmer| f1.username = f2.username
}

fact UniqueEmail{
    no disj f1,f2: Farmer| f1.email = f2.email
}

fact noUsernameWithoutFarmer {
all un: Username | one f: Farmer | f.username = un
}

//policy maker's code is unique
fact UniqueCode{
    no disj pm1,pm2: PolicyMaker| pm1.code = pm2.code 
}

/*
fact noPasswordWithoutFarmerOrPolicyMaker {
    all p: Password | ( some u: User |  u.password  = p)
}*/

//farm name is unique
fact UniqueFarmName {
    no disj f1, f2: Farm | f1.name = f2.name
}

//no farmname without farm
fact noFarmNameWithoutFarm {
    all fn: FarmName | one f: Farm | f.name = fn
}

//there are not two farms in the same position
fact UniqueFarmsPosition{
    no disj f1,  f2: Farm | f1.position = f2.position
}

//no farmer without farm
fact noFarmerWithoutFarm {
    all f: Farmer | one farm: Farm | farm.owner = f
}

//There is no wheater info with the same date and position with different temperature or wheater info
fact singleWheaterInfo{
    all w1, w2: WeatherInfo | (w1.position=w2.position and w1.date=w2.date)  implies (w1.temperature= w2.temperature and w1.basicInfo=w2.basicInfo)
}

//weather position equal farm position
fact weatherValidity{
	all f: Farm | f.position = f.weather.position
}

//no production without farm
fact noProductionWithoutFarm{
    all p: Production | one f: Farm | p in f.products
}

//no product without production
fact noProductWithoutProduction{
	all p: Product | one production: Production | p in production.type
}

//no different production of same type in one farm in one day
fact noProductionsOfSameType{
    no disj p1, p2: Product | one f: Farm | one p: Production | p1.name=p2.name and p1.date=p2.date and p in f.products and p.type.name=p1.name and p.type.name=p2.name 
}

//no product of a zero amount in a farm
fact noEmptyProduction {
    all p: Production | one f: Farm | p in f.products iff p.amount>0
}

//no message sent in the same instant by the same farmer
fact oneMessageAtTime{
    no disj m1, m2: Message | m1.sender=m2.sender and m1.date=m2.date and m1.time=m2.time and m1.content != m2.content
}

//every help have exacly one Solution
fact oneSolutionForOneHelp{
    all h: Help | one s: Solution | h.sender = s.receiver and h.typeOfProduction=s.typeOfProduction
}

//no sensor data without a farm
fact noSensorWithoutFarm{
    all s1, s2 : SensorData | one f: Farm | s1 in f.water and s2 in f.humidity
}

//all the farms are in the map
fact allFarmsMapped {
    all f: Farm | one m: Map | f in m.farms
}

//only one evaluation per month for a farm
fact singleEvaluation {
    no disj e1, e2: Evaluation | e1.receiver=e2.receiver and e1.date.month=e2.date.month and e1.date.year = e2.date.year
}

//the evaluation receiver must be the same of the owner of the farm on which is made
fact courrespondingOwner {
    all e: Evaluation | one farm: Farm | e in farm.evaluation and farm.owner = e.receiver
}

//only good farmer can make advice
fact howCanSubmitAnAdvice {
    all advice: Advice | one farm: Farm | one e: Evaluation | advice.sender=farm.owner and e in farm.evaluation and advice.date.month=e.date.month and advice.date.year=e.date.year and e.result = True
}

pred word{
	
	--#Farmer = 4
	#PolicyMaker = 1
	#Notification=0
	#Farm = 2
	
}
run word for 8

	