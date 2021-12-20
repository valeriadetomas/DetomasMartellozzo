
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
    month > 0 || month< 13
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

sig Production{
    type: one ProductName,
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
    date: one Date,
    time: one Time 
}

sig Help extends Notification{
    sender: one Farmer,
    receiver: one PolicyMaker,
    typeOfProduction: one Production
}
sig Advice extends Notification{
    sender: one Farmer,
    receiver: one PolicyMaker,
    typeOfProduction: one Production
}

sig Solution extends Notification{
    sender: one PolicyMaker,
    receiver: one Farmer,
    typeOfProduction: one Production
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

fact noSurnameWithoutFarmer {
all sur: Surname | one f: Farmer | f.surname = sur
}

//policy maker's code is unique
fact UniqueCode{
    no disj pm1,pm2: PolicyMaker| pm1.code = pm2.code 
}

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
	all p: ProductName | one production: Production | p = production.type
}

//no different production of same type in one farm in one day
fact noProductionsOfSameType{
    no disj p1, p2: Production | one f: Farm  | p1.type=p2.type and p1 in f.products and p2 in f.products and p1.date=p2.date
}

//no product of a zero amount in a farm
fact noEmptyProduction {
    all p: Production | one f: Farm | p in f.products iff p.amount>0
}

//all message are stored in the forum
fact messageValidity{
	all m:Message | one f:Forum | m in f.messages
}


//all message have different body
fact noEqualMessages{
	no disj m1, m2: Message | m1.content = m2.content
}

//no equal notification
fact noEqualNotifications{
	no disj n1, n2: Notification | n1.body = n2.body
}

//no message sent in the same instant by the same farmer
fact oneMessageAtTime{
    no disj m1, m2: Message | m1.sender=m2.sender and m1.date=m2.date and m1.time=m2.time 
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
fact evaluationValidity{
	all f: Farm | #f.evaluation >0 implies f.owner = f.evaluation.receiver
}

fact noEvaluationWithoutFarm{
	all e: Evaluation | one f: Farm | f.owner=e.receiver implies e in f.evaluation
}

//only good farmer can make advice
fact howCanSubmitAnAdvice {
    all advice: Advice | one farm: Farm | one e: Evaluation | advice.sender=farm.owner and e in farm.evaluation and advice.date.month=e.date.month and advice.date.year=e.date.year and e.result = True
}



pred word1{
	
	//registration of 2 farmer only
	#PolicyMaker = 0
	#Notification=0
	#Farmer = 2
	#Code = 0
	#MessageContent = 0

}
run word1 for 3



pred word3{

	//messages in the forum
	#Farmer = 2
	#Message = 4
	#PolicyMaker = 0
	#Code = 0
	#Production = 2
	#Date = 2
	#Time = 3

}
run word3 for 5





	