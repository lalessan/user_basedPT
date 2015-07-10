# -*- coding: utf-8 -*-
# <nbformat>3.0</nbformat>

# <codecell>

import subprocess
import pandas as pd
import os
import datetime as dt
from collections import defaultdict
import matplotlib.pyplot as plt
import matplotlib.dates as md
import matplotlib.colors as col
import math
import os
from scipy.stats import mode
import csv
from math import *
from collections import Counter
import numpy as np

def create_adjacency_matrix(folder):
    #To transform the files to the adjacency matrix format using AWK
    fichier=folder+"/stop_times.txt "
    fichier2=folder+"/adjacency2.txt "
    COMMAND0="kprice=$(awk -F', ' -vfield=trip_id 'NR==1{for(i=1;i<=NF;i++){if($i==field){print i;exit}}}' "+folder+"/stop_times.txt)"
    COMMAND1="ksize=$(awk -F', ' -vfield=stop_sequence 'NR==1{for(i=1;i<=NF;i++){if($i==field){print i;exit}}}' "+folder+"/stop_times.txt)"
    COMMAND2=" head -1 "+folder+"/stop_times.txt >"+folder+"/stop_times3.txt ; tail -n +2 "+folder+"/stop_times.txt | sort -k \"$kprice\"2 -k\"$ksize\"1 >>"+folder+"/stop_times3.txt"
    COMMAND="cat "+folder+"/stop_times3.txt "+"| awk -v cols=trip_id,departure_time,stop_id,stop_sequence 'BEGIN{FS=\" |,\";old_trip=0;old_id=0; n=split(cols,col);for (i=1; i<=n; i++) s[col[i]]=i}NR==1 {for(f=1; f<=NF; f++) if ($f in s) {c[s[$f]]=f}; next;} {if ($c[1]==old_trip) {print old_id \",\" $c[3] \",\" $c[1] \",\" $c[2] \",\" (substr($c[2],1,2)-start_hour)*60+(substr($c[2],4,2)-start_minute) \",\"  $c[4]-1} else{start_hour=substr($c[2],1,2); start_minute=substr($c[2],4,2)};old_id=$c[3];old_trip=$c[1]}' > "+fichier2
    subprocess.call(COMMAND0, shell=True)
    subprocess.call(COMMAND1, shell=True)
    subprocess.call(COMMAND2, shell=True)
    subprocess.call(COMMAND, shell=True)
    subprocess.call("rm "+folder+"/stop_times3.txt ",shell=True)
    
class AutoVivification(dict):
    """Implementation of perl's autovivification feature."""
    def __getitem__(self, item):
        try:
            return dict.__getitem__(self, item)
        except KeyError:
            value = self[item] = type(self)()
            return value
        
def daterange(start_date, end_date):
    #this function define a range of dates
    for n in range(int ((end_date +dt.timedelta(days=1)- start_date).days)):
        yield start_date + dt.timedelta(n)
        
        
def average(s): return sum(s) * 1.0 / len(s)

def standard_deviation(s):
    mean=average(s)
    variance = map(lambda x: (x - mean)**2, s)
    return math.sqrt(average(variance))

        
def most_common_oneliner(L):
    from itertools import groupby as g
    return max(g(sorted(L)), key=lambda(x, v):(len(list(v)),-L.index(x)))[0]


import heapq
def single_source_dijkstra(G,source,target=None,cutoff=None,weight='weight',route='route', route_type='route_type',penalty=5,mappa=0):
    #the modified Dijkstra Algorithm
    if source==target:
        return ({source:0}, {source:[source]})
    dist = {}  # dictionary of final distances
    paths = {source:[source]}  # dictionary of paths
    seen = {source:0}
    routetypes={source:[None]}
    routes={source:[None]}
    routetimes={source:[0]}
    lenpat={}
    fringe=[] # use heapq with (distance,label) tuples
    heapq.heappush(fringe,(0,source,None,None))
    while fringe:
        (d,v,r,t)=heapq.heappop(fringe)
        if v in dist:
            continue # already searched this node.
        dist[v] = d
        lenpat[v]=len(paths[v])-1
        if v == target:
            break
        #for ignore,w,edgedata in G.edges_iter(v,data=True):
        #is about 30% slower than the following
        if G.is_multigraph():
            edata=[]
            if r==None:
                for w,keydata in G[v].items():
                    minweight=min((dd for k,dd in keydata.items()),key=lambda x: x['weight'])
                    edata.append((w,minweight))
            else:
                if mappa!=0:
                    for w,keydata in G[v].items():
                        minweight=min(({'weight':dd['weight']+mappa[t][dd['route_type']]*(dd['route']!=r),'route':dd['route'],'route_type':dd['route_type']} for k,dd in keydata.items()),key=lambda x:x['weight'] )
                        edata.append((w,minweight))
                else:
                    for w,keydata in G[v].items():
                        minweight=min(({'weight':dd['weight']+penalty*(dd['route']!=r),'route':dd['route'],'route_type':dd['route_type']} for k,dd in keydata.items()),key=lambda x:x['weight'] )
                        edata.append((w,minweight))


                
        else:
            edata=iter(G[v].items())

        for w,edgedata in edata:
            vw_dist = dist[v] + edgedata.get(weight,1)
            lenght=lenpat[v]+1
            if cutoff is not None:
                if lenght>cutoff:
                    continue
            if w in dist:
                if vw_dist < dist[w]:
                    raise ValueError('Contradictory paths found:',
                                     'negative weights?')
            elif w not in seen or vw_dist < seen[w]:
                rr=edgedata.get(route,1)
                rr2=edgedata.get(route_type,1)
                seen[w] = vw_dist
                heapq.heappush(fringe,(vw_dist,w,rr,rr2))
                paths[w] = paths[v]+[w]
                routetimes[w]=routetimes[v]+[str(vw_dist)]
                #print routetypes[v]
                routetypes[w]=routetypes[v]+[rr2]
                routes[w]=routes[v]+[rr]
    if target==None:
        return (dist,paths,routetypes,routetimes,routes)
    else:
        return dist[target],paths[target],routetypes[target],routetimes[target],routes[target]


def all_paths_dijkstra(G,target=None,cutoff=None,weight='weight',route='route',route_type='route_type',penalty=5,mappa=0):
    kk=0
    distances=defaultdict(dict)
    allthepaths=defaultdict(dict)
    routetypes=defaultdict(dict)
    routetimes=defaultdict(dict)
    routes=defaultdict(dict)
    for n in G.nodes():
        kk+=1
        distances[n],allthepaths[n],routetypes[n],routetimes[n],routes[n]=single_source_dijkstra(G,n,target=target,weight=weight,cutoff=cutoff,route=route,penalty=penalty,mappa=mappa)
        if kk%10==0:
            print kk,

    return distances,allthepaths,routetypes,routetimes,routes


def distance(lat1,lat2,lon1,lon2):
    lat1=radians(lat1)
    lat2=radians(lat2)
    lon1=radians(lon1)
    lon2=radians(lon2)
    dlon = lon2 - lon1
    dlat = lat2 - lat1
    a = (sin(dlat/2))**2 + cos(lat1) * cos(lat2) * (sin(dlon/2))**2
    c = 2 * atan2(sqrt(a), sqrt(1-a))
    return 6373.0* c

def most_common(lst):
    return max(set([tuple(i) for i in lst]), key=lst.count)

# <codecell>

import time
    
class dataset:
    # this class is initialised with a folder containing the files in GTFS standard format
    def __init__(self,folder):
        self.df_calendar=pd.read_csv(folder+'/calendar.txt',dtype='object')
        self.df_calendar_dates=pd.read_csv(folder+'/calendar_dates.txt',dtype='object')
        self.df_trips=pd.read_csv(folder+'/trips.txt',dtype='object')
        if not os.path.isfile(folder+'/adjacency2.txt'):
            create_adjacency_matrix(folder)
        self.df_adjacency=pd.read_csv(folder+'/adjacency2.txt',header=None,dtype='object')
        self.df_adjacency.columns=['Source','Target','trip_id','departure_time','time_from_start','n_sequence']
        self.df_adjacency['time_from_start']=self.df_adjacency['time_from_start'].astype(int)

        self.df_adjacency['n_sequence']=self.df_adjacency['n_sequence'].astype(int)

        self.df_stops=pd.read_csv(folder+'/stops.txt',dtype='object')
        self.df_routes=pd.read_csv(folder+'/routes.txt',dtype='object')
        self.folder=folder
        
    def select_days(self, selected='weekday',nweeks=4):
        #to select the range of dates. selected='weekdays' or 'weekends' and nweeks is the number of weeks in the window length
        map_service=dict(zip(self.df_trips.trip_id, self.df_trips.service_id)) #trip to service
        convert = lambda x: dt.datetime(year=int(str(x)[0:4]), month=int(str(x)[4:6]), day=int(str(x)[6:8]))
        self.df_calendar['start_date2']=self.df_calendar.start_date.apply(convert)
        self.df_calendar['end_date2']=self.df_calendar.end_date.apply(convert)
        self.df_calendar_dates['date2']=self.df_calendar_dates.date.apply(convert)
        self.df_calendar_dates=self.df_calendar_dates.rename(columns={'service_id ':'service_id'})
        map_weekdays = {0:'monday', 1:'tuesday', 2:'wednesday', 3:'thursday', 4:'friday', 5:'saturday', 6:'sunday'}

        #create a list of the total days and total number of services on that day
        min_day=min(list(self.df_calendar['start_date2'])+list(self.df_calendar_dates['date2']))
        max_day=max(list(self.df_calendar['end_date2'])+list(self.df_calendar_dates['date2']))

        period_measures=[i for i in daterange(min_day,max_day)]
        
        
        def service_activity(df):    
            for day in daterange(df['start_date2'],df['end_date2']):
                active=df[map_weekdays[day.weekday()]]
                if active=='1':
                    try:
                        services_per_day[period_measures.index(day)]+=1 #number of services every day
                    except ValueError:
                        print 'here0', day
                    services[day].append(df['service_id']) #map day to which services are active on that day




        def exception(df):
            if df['exception_type']=='1':
                services_per_day[period_measures.index(df['date2'])]+=1
                services[df['date2']].append(df['service_id'])
            if df['exception_type']=='2':
                try:
                    services[df['date2']].remove(df['service_id'])
                    services_per_day[period_measures.index(df['date2'])]-=1
                except ValueError: 
                    pass;
                
        services=defaultdict(list)
        services_per_day=[0]*len(period_measures)
        self.df_calendar.apply(service_activity,axis=1); 
        self.df_calendar_dates.apply(exception, axis=1);
        weekends=[day for day in period_measures if day.weekday() == 6 or day.weekday() == 5 ]
        services_weekends=[services_per_day[period_measures.index(i)] for i in weekends]
        other_days=[day for day in period_measures if day not in weekends]
        services_other_days=[services_per_day[period_measures.index(i)] for i in other_days]


        if not os.path.exists(self.folder+'/outputs/Calendar'):
            os.makedirs(self.folder+'/outputs/Calendar')

        #count the number of trips per day
        serie=pd.DataFrame([map_service[i] for i in self.df_adjacency.groupby('trip_id').groups.keys()]).rename(columns={0:'service_id'})
        serie=serie.groupby('service_id').size().reset_index().rename(columns={0:'Ntripsperday'})
        map_serie=serie.set_index('service_id')['Ntripsperday'].to_dict()
        trips_per_day=[sum([(map_serie[i]) for i in services[day]]) for day in period_measures]

        #count the number of services on weekdays and weekends
        trip_weekends=[trips_per_day[period_measures.index(i)] for i in weekends]
        trip_other_days=[trips_per_day[period_measures.index(i)] for i in other_days]

        #calculate the interesting period
        other_days_window=[x for (x,y) in zip(other_days,trip_other_days)] 
        trips_other_days_window=[y for (x,y) in zip(other_days,trip_other_days)]
        weekends_window=[day for day in weekends if day in daterange(other_days_window[0],other_days_window[-1])]
        trips_weekends_window=[y for (x,y) in zip(weekends,trip_weekends) if x in weekends_window]
        
        if selected=='weekday':
            #calculate the mean and standard deviation of number of trips for a window of (nweeks) weeks
            nweeks=nweeks
            weeks=defaultdict(list)
            for day in other_days_window:
                WeekNum= day.isocalendar()[1]
                weeks[WeekNum].append(day)
            
            f = open(self.folder+'/outputs/Calendar/AveragesWeeks.txt','w')
             # python will convert \n to os.linesep
            std_min_inv=np.inf
            if len(weeks)<nweeks:
                print 'your dataset only contains '+str(len(weeks))+' weeks. Choose a shorter window'
            for index,week in enumerate(weeks.keys()[:-(nweeks-1)]):
                window_weeks=[weeks.keys()[k] for k in range(index,index+nweeks)]
                trips_week=[[trips_other_days_window[other_days_window.index(day)] for day in weeks[i]] for i in window_weeks ]
                l = [val for subl in trips_week for val in subl]
                string='weeks:'+str( window_weeks)+ '    mean:'+str(int(average(l)))+'    std:'+str(int(standard_deviation(l)))
                f.write(string+'\n')
                if standard_deviation(l)<std_min_inv:
                    selected_weeks=window_weeks
                    std_min_inv=standard_deviation(l)

            f.close()

            #selected weeks
            selected_days=[x for x in other_days_window if x.isocalendar()[1] in selected_weeks] 
            trip_selected=[y for (x,y) in zip(other_days_window,trips_other_days_window) if x in selected_days]
            
            
        elif selected=='weekend':
            #calculate the mean and standard deviation of number of trips for a window of (nweeks) weeks
            nweeks=nweeks
            weeks=defaultdict(list)
            for day in weekends_window:
                WeekNum= day.isocalendar()[1]
                weeks[WeekNum].append(day)
            print len(weeks),
            if len(weeks)<nweeks:
                print 'your dataset only contains '+str(len(weeks))+' weeks. Choose a shorter window'
                
            f = open(self.folder+'/outputs/Calendar/AveragesWeeks.txt','w')
             # python will convert \n to os.linesep
            std_min_inv=np.inf
            for index,week in enumerate(weeks.keys()[:-(nweeks-1)]):
                window_weeks=[weeks.keys()[k] for k in range(index,index+nweeks)]
                trips_week=[[trips_weekends_window[weekends_window.index(day)] for day in weeks[i]] for i in window_weeks ]
                l = [val for subl in trips_week for val in subl]
                string='weeks:'+str( window_weeks)+ '    mean:'+str(int(average(l)))+'    std:'+str(int(standard_deviation(l)))
                f.write(string+'\n')
                if standard_deviation(l)<std_min_inv:
                    selected_weeks=window_weeks
                    std_min_inv=standard_deviation(l)

            f.close()


            #selected weeks
            selected_days=[x for x in weekends_window if x.isocalendar()[1] in selected_weeks] 
            trip_selected=[y for (x,y) in zip(weekends_window,trips_weekends_window) if x in selected_days]
            
        #write trips per day on file
        zipped=zip(other_days_window,trips_other_days_window)+zip(weekends_window,trips_weekends_window)
        f=open(self.folder+'/outputs/Calendar/trips_per_day.txt','w')
        f.write('day,trips_per_day\n')
        for (x,y) in zipped:
            string=['{:02d}'.format(x.year)+'{:02d}'.format(x.month)+'{:02d}'.format(x.day),str(y)]
            f.write(','.join(string)+'\n')
        f.close()


        active_services=[]
        for day in selected_days:
            active_services.append((day,[x for x in services[day]]))
        self.active_services=dict(active_services)
        f=open(self.folder+'/outputs/Calendar/selected_days.txt','w')
        for (x,y) in active_services:
            string=['{:02d}'.format(x.year)+'{:02d}'.format(x.month)+'{:02d}'.format(x.day), ','.join([str(i) for i in y])]
            f.write(','.join(string)+'\n')
        f.close()


        fig = plt.figure(figsize=(40,5))
        plt.yscale('log')
        other_days_window=md.date2num(other_days_window)
        weekends_window=md.date2num(weekends_window)
        selected_days=md.date2num(selected_days)
        p1=plt.plot(other_days_window, trips_other_days_window,'o',label='Weekdays')
        p2=plt.plot(weekends_window, trips_weekends_window,"or", label='Weekends')
        p3=plt.plot(selected_days,trip_selected,'ok',label='Selected_days')
        xfmt = md.DateFormatter('%b-%Y')

        ax=plt.gca()
        xfmt = md.DateFormatter('%b-%Y')
        ax.xaxis.set_major_formatter(xfmt)
        plt.yticks(fontsize=20)
        plt.xticks( rotation=25,fontsize=20)
        plt.ylabel('Number of trips per day',fontsize=20)
        plt.legend(fontsize=20)
        plt.savefig(self.folder+'/outputs/Calendar/calendar_trips.png',bbox_inches='tight')
        plt.close()
        
    def parent_stations(self):
        #map stops to parent stations
        self.df_stops['parent_station']=self.df_stops['parent_station'].replace(to_replace="",value=np.nan)
        self.df_stops['parent_station']=self.df_stops['parent_station'].fillna(self.df_stops.stop_id)
        self.map_parent=dict(zip(self.df_stops['stop_id'],self.df_stops['parent_station']))       
        
        
        if self.map_parent.values()==self.map_parent.keys():
            map_names=dict()
            for index,row in self.df_stops.iterrows():
                name=row['stop_name']
                if name in map_names.keys():
                    self.map_parent[row['stop_id']]=map_names[name]
                else:
                    self.map_parent[row['stop_id']]=row['stop_id']
                    map_names[row['stop_name']]=row['stop_id']
                    
                    
        #if I want to use the transfer file
        
        
        #if I want to use the clustering




        map_parent_opposite=defaultdict(list)
        for items in self.map_parent.items():
            map_parent_opposite[items[1]].append(items[0])

        map_lat=dict(zip(self.df_stops.stop_id,[np.float(i) for i in self.df_stops.stop_lat]))
        map_lon=dict(zip(self.df_stops.stop_id,[np.float(i) for i in self.df_stops.stop_lon]))
        
        map_names=dict(zip(self.df_stops.stop_id,self.df_stops.stop_name))
        map_stops=dict()
  
        self.map_latitude=dict()
        self.map_longitude=dict()
        for item in map_parent_opposite.items():
            map_stops[item[0]]=most_common_oneliner([map_names[i] for i in item[1]])
            self.map_latitude[item[0]]=np.median([map_lat[i] for i in item[1]])
            self.map_longitude[item[0]]=np.median([map_lon[i] for i in item[1]])

            
        if not os.path.exists(self.folder+'/outputs/Stops'):
            os.makedirs(self.folder+'/outputs/Stops')

        outfile = open(self.folder+'/outputs/Stops/Parents_names.txt', 'w' )
        outfile.write('stop_id,name_desc\n')
        for key, value in  map_stops.items():
            outfile.write( str(key) + ',' + str(value) + '\n' )
        outfile.close()

        df_stops_final=pd.DataFrame(list(set(self.map_parent.values())),columns=['stop_id'])
        df_stops_final['stop_lat']=df_stops_final['stop_id'].map(self.map_latitude)
        df_stops_final['stop_lon']=df_stops_final['stop_id'].map(self.map_longitude)
        df_stops_final.to_csv(self.folder+'/outputs/Stops/Parents_location.txt',index=False,columns=['stop_id','stop_lat','stop_lon'])


        outfile = open( self.folder+'/outputs/Stops/Parents_dictionary.txt', 'w' )
        headers = ['stop_id', 'parent_id']
        outfile.write('stop_id,parent_id\n')
        for key, value in  self.map_parent.items():
            outfile.write( key + ',' + value + '\n' )
        outfile.close()

        
    def routes(self,minhour=8,maxhour=10):        
        #average the behaviour between minhour and maxhour
        map_route=dict(zip(self.df_trips.trip_id,self.df_trips.route_id),dtype='object') #trip to route
        map_service=dict(zip(self.df_trips.trip_id, self.df_trips.service_id),dtype='object') #trip to service
        map_trip=dict(zip(self.df_trips.trip_id,self.df_trips.trip_headsign),dtype='object') #trip to headsign
        self.map_type=dict(zip(self.df_routes[self.df_routes.columns[0]],self.df_routes.route_type),dtype='object') #route to route_type


        minhoursmaxhours=str(minhour)+'-'+str(maxhour)

        self.df_adjacency['time']=self.df_adjacency['departure_time'].apply(lambda x: int(x[0:2]))
        self.df_adjacency=self.df_adjacency[(self.df_adjacency['time']<maxhour) & (self.df_adjacency['time']>=minhour)]

        frequency=defaultdict(list)
        stops1=defaultdict(list)
        for day in sorted(self.active_services.keys()): 
            print day
            #The services active per day 
            active_services=self.active_services[day] 

            #select trips active on average day
            df_adjacency_day=self.df_adjacency[self.df_adjacency['trip_id'].map(map_service).isin(active_services)].reset_index()

            df_adjacency_day['route_id']=df_adjacency_day['trip_id'].map(map_route)
            #from stops to parent stations        
            df_adjacency_day['Source']=df_adjacency_day['Source'].map(self.map_parent) 
            df_adjacency_day['Target']=df_adjacency_day['Target'].map(self.map_parent) 
            #avoid selfloops
            df_adjacency_day=df_adjacency_day[df_adjacency_day['Source']!=df_adjacency_day['Target']]
            #map to trip id
            df_adjacency_day['trip_head']=df_adjacency_day['trip_id'].map(map_trip)
            #dictionary route, headsign to longest trip
            sizes=df_adjacency_day.groupby(['route_id','trip_id','trip_head']).size().reset_index()
            df=sizes.groupby(['route_id','trip_head']).max().reset_index()
            tripmap=defaultdict(dict)
            for route in list(set(df.route_id)):
                a=df[df['route_id']==route]
                tripmap[route].update(dict(zip(a.trip_head, range(len(a)))))
            trips=list(set(df.trip_id))
            df_adjacency_day['trip_head2']=df_adjacency_day.apply(lambda x:tripmap[x['route_id']][x['trip_head']],axis=1)

            for index, row in df_adjacency_day.groupby(['Source','Target','route_id','trip_head2']).size().reset_index().iterrows():
                frequency[(row['route_id'],row['trip_head2'])].append(row[0])
            #Only longest trips
            df_adjacency_day=df_adjacency_day[df_adjacency_day['trip_id'].isin(trips)]
            gp1=df_adjacency_day.groupby(['route_id','trip_head2'])

            for k,group in gp1:
                gruppo=group.sort('n_sequence')
                Sources=list(gruppo.Source)
                Targets=list(gruppo.Target)
                Times=list(gruppo['time_from_start'])
                #tr=list(gruppo.trip_head)[0]
                stops1[k].append([(Sources[0],0)]+[(Targets[index],Times[index]) for index in range(len(Times))])
                
                '''
                for index,target in enumerate(Targets):
                    stops1[k][target].append((index+1,Times[index]))
                '''
                    
        self.frequency=dict()
        for key in frequency.keys():
            somma=int(round(float(sum(frequency[key]))/len(frequency[key])))
            self.frequency[key]=somma
            
        self.stops=defaultdict(lambda: defaultdict(list))


        #here I take for every route and every stop,(if the number on the route is the same) the time as the average time on the 20 days

        for route,values in stops1.items():
            #1 take the most frequent route
            k=[[i[0] for i in values[k]] for k in range(len(values))] 
            c=list(most_common(k))
            indexes=[n for n,i in enumerate(k) if i==c]
            mean_tempi=[np.mean(item) for item in np.array([[i[1] for i in values[k]] for k in range(len(values)) if k in indexes]).T]
            for n,stop in enumerate(c):
                self.stops[route][stop].append((n,mean_tempi[n]))
        '''  
        #here I take for every route and every stop,(if the number on the route is the same) the time as the average time on the 20 days
        for route,values in stops1.items():
            #1 take the most frequent route
            [[i[1] for i in values[k]] for k in values]
            lista=[]
            for stop,lista_stop in stops1[route].items():
                lenghts=[]
                counts=Counter([i[0] for i in lista_stop])
                number_selected=[i[0] for i in counts.items() if i[1]==max(counts.values())]
                values=[[i for i in lista_stop if i[0]==k] for k in number_selected]
                values=[(i[0][0],sum([float(k[1]) for k in i])/len(i)) for i in values]        
                self.stops[route][stop]=values
        '''
        if not os.path.exists(self.folder+'/outputs/Routes'):
            os.makedirs(self.folder+'/outputs/Routes')
        #write stops(route) on file
        headers=['route_id','route_direction','stop_id','stop_sequence','time_sequence']
        ofile = open(self.folder+'/outputs/Routes/Routes_dictionary'+minhoursmaxhours+'.txt', 'wb')
        writer = csv.writer(ofile)
        writer.writerow(headers) 
        for route in self.stops.keys():
            for stop in sorted(self.stops[route].items(),key=lambda x:x[1]):
                for i,t in self.stops[route][stop[0]]:
                    u=[route[0],route[1],stop[0],i,t]
                    writer.writerow(u) 

        ofile.close()

        #write frequencies(route) on file
        headers=['route_id','route_direction','frequency_day']
        ofile = open(self.folder+'/outputs/Routes/Routes_frequency'+minhoursmaxhours+'.txt', 'wb')
        writer = csv.writer(ofile)
        writer.writerow(headers) 
        for item in sorted(self.frequency.items(),key=lambda x:x[0]):
            writer.writerow([item[0][0],item[0][1],item[1]]) 
        ofile.close()
        
    def shortest_paths(self,n_changes=3,minhour=8,maxhour=10): 
        #calculate shortest paths
    #load the transfer time
        average_transfers_RATP=pd.read_csv('./Average_transfer_time.txt',dtype='object')
        map_transfers=defaultdict(dict)
        for index,row in average_transfers_RATP.iterrows():
            map_transfers[row[0]][row[1]]=float(row[2])/60  
            map_transfers[row[1]][row[0]]=float(row[2])/60  
        
   
        map_transfers['7']=map_transfers['3']
        map_transfers['0']['7']=map_transfers['0']['3']
        map_transfers['1']['7']=map_transfers['1']['3']
        map_transfers['2']['7']=map_transfers['2']['3']
        map_transfers['3']['7']=map_transfers['3']['3']
        map_transfers['4']=map_transfers['3']
        map_transfers['0']['4']=map_transfers['0']['3']
        map_transfers['1']['4']=map_transfers['1']['3']
        map_transfers['2']['4']=map_transfers['2']['3']
        map_transfers['3']['4']=map_transfers['3']['3']


        import networkx as nx

        data=[]

        for route in self.stops.keys():
            route_type=self.map_type[route[0]]
            allstops=sorted(self.stops[route].items(),key=lambda x: x[1][0][0])
            for index,tuple1 in enumerate(allstops[:-1]):
                for tuple2 in allstops[index+1:]:
                    data.append((tuple1[0],tuple2[0],dict(weight=(float(60*(maxhour-minhour))/(2*self.frequency[route])+tuple2[1][0][1]-tuple1[1][0][1]),route=route,route_type=route_type)))

        G=nx.MultiDiGraph(data)
        self.times,allpaths,modes,routetimes,routes1=all_paths_dijkstra(G,cutoff=3,weight='weight',penalty=5,mappa=map_transfers)

    def heatmap(self,selection=1):
        #Compute the heatmap
        t=time.time()
        self.distances=defaultdict(dict)
        for a in self.times.keys():
            for b in self.times[a].keys():
                self.distances[a][b]=distance(self.map_latitude[a],self.map_latitude[b],self.map_longitude[a],self.map_longitude[b])
        #create tuples distance vs time

        print 'here1',time.time()-t
        data1=[]
        tuples=[]

        for node1 in self.times.keys():
            for node2 in self.times[node1].keys():
                data1.append((self.distances[node1][node2],self.times[node1][node2]))
                tuples.append((node1,node2))
                   
        x,y = zip(*data1)
        xbins=int(max(x)-min(x))/0.1
        ybins=int((max(y)-min(y)))
        H, xedges,yedges = np.histogram2d(x,y,bins=(xbins,ybins))    

        d=np.digitize(x, bins=xedges)    
        d2=np.digitize(y, bins=yedges)
        mappa=defaultdict(lambda: defaultdict(list))
        print 'here2',time.time()-t
        for node_index,xbin in enumerate(d):
            mappa[xbin-1][d2[node_index]-1].append(tuples[node_index])
        closenodes=[]
        farnodes=[]
        H2=np.zeros(shape=(H.shape))
        print 'here3',time.time()-t,len(H)

        for k,x_histo in enumerate(H):
            nvalues=float(sum(x_histo))*1/100

            n=0
            for i1,value in enumerate(x_histo):
                closenodes.extend(mappa[k][i1])
                H2[k][i1]=H[k][i1] 
                if n>nvalues:
                    break;
                n+=value

            n=0
            for i2,value in reversed(list(enumerate(x_histo))):
                farnodes.extend(mappa[k][i2])  
                if n>nvalues:
                    break
                n+=value
        print 'here4',time.time()-t
        H_log=np.log10(H)
        extent = [xedges[0], xedges[-1], yedges[0], yedges[-1]]


        fig = plt.figure(figsize=(20,10))
        ax = fig.add_subplot(121)
        cax =ax.imshow(H_log.T, extent=extent, aspect='auto',origin='lower')   
        ax.ticklabel_format(style='sci', scilimts=(0,0))
        ax.set_xlabel('Distance(Km)',fontsize=30)
        ax.set_ylabel('Time(min)',fontsize=30)
        ax.set_title('HeatMap',fontsize=25)
        ax.tick_params(labelsize=30)
        ax.set_xlim(0,25)
        ax.set_ylim(0,150)
        plt.setp(ax.get_xticklabels(), fontsize=30)

        cb=fig.colorbar(cax)
        cb.set_label(r'\#of edges(log10)',fontsize=30) 
        cb.ax.tick_params(labelsize=15)


        x_new=[self.distances[i[0]][i[1]] for i in closenodes]#+farnodes[n_conn]]
        y_new=[self.times[i[0]][i[1]] for i in closenodes]#+farnodes[n_conn]]

        n, _ = np.histogram(x_new, bins=xbins)
        sy, _ = np.histogram(x_new, bins=xbins, weights=y_new)
        sy2, _ = np.histogram(x_new, bins=xbins, weights=[i*i for i in y_new])
        mean = sy / n
        mean2=[i for i in mean if str(i)!='nan']
        xmean=[i for index,i in enumerate(xedges[:-1]) if str(mean[index])!='nan']
        stdmean=[i for index,i in enumerate(np.sqrt(sy2/n - mean*mean)) if str(mean[index])!='nan']


        H_log2=np.log10(H2)
        extent = [xedges[0], xedges[-1], yedges[0], yedges[-1]]
        ax2 = fig.add_subplot(122)
        cax2=ax2.imshow(H_log2.T, extent=extent, aspect='auto',origin='lower',cmap=cax.cmap)
        norm=col.Normalize(0, vmax=H_log.T.max())
        cax2.set_norm(norm)
        ax2.set_xlabel('distance(Km)',fontsize=30)
        ax2.set_ylabel('time(min)',fontsize=30)
        ax2.set_xlim(0,25)
        ax2.set_ylim(0,150)
        ax2.set_title('Selected pairs',fontsize=25)
        plt.setp(ax2.get_xticklabels(), fontsize=30)
        ax2.tick_params(labelsize=30)

        cb2=fig.colorbar(cax2)
        cb2.set_label('\#of edges(log10)',fontsize=30) 
        cb2.ax.tick_params(labelsize=15)
        if not os.path.exists(self.folder+'/outputs/Selection/'):
            os.makedirs(self.folder+'/outputs/Selection/')
        plt.savefig(self.folder+'/outputs/Selection/HeatMapSelection.png',bbox_inches='tight')


        
    def produce_map(self,im=None,minlat=None,maxlat=None,minlon=None,maxlon=None):
        if im!=None:
            im=plt.imread(im)
            fig=plt.figure(figsize=(40,32))
            plt.imshow(im,extent = [minlon,maxlon,minlat,maxlat],aspect='auto',alpha=0.7)
            plt.xlim([minlon,maxlon])
            plt.ylim([minlat,maxlat])
        else:
            fig=plt.figure(figsize=(40,32))
            
        plt.tick_params(labelsize=90)   
        locs, labels = plt.xticks()
        plt.setp(labels, rotation=45)
        locs2,labels2=plt.yticks()
        plt.setp(labels2, rotation=45)
        p2=plt.plot([0,0],[0,0],color='r',linewidth=max(df.weight)*m+c,label='{0} transits '.format(str(int(max(df.weight)))))
        p1=plt.plot([0,0],[0,0],color='r',linewidth=min(df.weight)*m+c,label='{0} transits '.format(str(int(min(df.weight)))))
        plt.legend(prop={'size':80})
        t.set_y(1.03) 
        plt.subplots_adjust(top=0.86) 
        m=float(15-2)/(max(df['weight'])-min(df['weight']))
        if max(df['weight'])==min(df['weight']):
            m=float(15-2)/(max(df['weight'])-min(df['weight']))

        c=2-min(df['weight'])*m
        for stop in self.stops:
            plt.scatter(map_position2[stop],map_position1[stop],s=50,color=color)
        for index,row in df.iterrows():
            plt.plot([map_position2[row[1]], map_position2[row[0]]],
                     [map_position1[row[1]], map_position1[row[0]]],color=color,linewidth=row[2]*m+c)


        filefigure=filename.replace('/Networks','/Maps').replace('.txt','.png')
        plt.savefig(filefigure,bbox_inches='tight')
        plt.close(fig)
        
    

# <codecell>


