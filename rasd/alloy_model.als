sig Password{}
sig UserName{}
sig Surname{}
sig Email{}
sig Code{}

sig Farmer{
    name: one UserName,
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

sig Forum{
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