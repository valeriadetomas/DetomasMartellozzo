sig Password{}
sig Username{}
sig Surname{}
sig Email{}
sig Code{}

sig Farmer{
    username: one Username,
    surname: one Surname,
    email: one Email,
    password: one Password
}

sig PolicyMaker{
    code: one Code, 
    password: one Password
}

sig Date{}
sig Time{}
sig MessageContent{}

sig Message{
    date: one Date,
    time: one Time,
    content: one MessageContent,
    sender: Farmer
}

one sig Forum{
    messages: some Message
}

sig ProductName{}

sig Product{
    name: one ProductName
}

sig Production{
    type: one Product,
    amount: one Int
}

sig SensorData{
    quantity: Int, 
    date: Date
}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig Notification{
    body: MessageContent,
    typeOfProduction: Production,
    date: Date,
    time: Time 
}

sig Help extends Notification{
    sender: Farmer,
    receiver: PolicyMaker
}
sig Advice extends Notification{
    sender: Farmer,
    receiver: PolicyMaker
}

sig Solution extends Notification{
    sender: PolicyMaker,
    receiver: Farmer
}

sig Evaluation extends Notification{
    sender: PolicyMaker,
    receiver: Farmer,
    result: Bool
}

sig Position {}
sig Weather{}

sig WeatherInfo{
    basicInfo: Weather,
    temperature: Int,
    position: Position,
    date: Date
}

sig FarmName{}

sig Farm{
    name: one FarmName,
    owner: one Farmer,
    products: some Production,
    water: SensorData,
    humidity: SensorData,
    position: Position, 
    weather: some WeatherInfo, 
    evaluation: Evaluation
}

sig Map{
    farms: some Farm
}


//Bool can only be true or false
fact boolean{
    True + False = Bool
}

//Uniquness of farmer's username and email
fact UniqueUsernames{
    no disj f1,f2: Famrer| f1.username = f2.username
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

fact noPasswordWithoutFarmerOrPolicyMaker {
    (all p: Password | one f: Farmer | f.password = p) or 
    (all p: Password | one pm: PolicyMaker | pm.password = p) 
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
fact noFamrerWithoutFarm {
    all f: Farmer | one farm: Farm | farm.farmer = f
}

//There is no wheater info with the same date and position with different temperature or wheater info
