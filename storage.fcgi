#!/usr/bin/python
import flask
import flup.server.fcgi
import os
import sqlalchemy
import sqlalchemy.ext.declarative
import sqlalchemy.orm
import time

engine = sqlalchemy.create_engine(
    sqlalchemy.engine.url.URL(
        drivername='mysql',
        database='andersk+pwmgr',
        query={'read_default_file': os.path.expanduser('~/.my.cnf')},
    ),
    isolation_level="SERIALIZABLE",
)

db_session = sqlalchemy.orm.scoped_session(sqlalchemy.orm.sessionmaker(bind=engine))

Base = sqlalchemy.ext.declarative.declarative_base()
Base.query = db_session.query_property()

class Item(Base):
    __tablename__ = 'items'
    id = sqlalchemy.Column(sqlalchemy.String(64), primary_key=True)
    data = sqlalchemy.Column(sqlalchemy.LargeBinary, nullable=False)

Base.metadata.create_all(bind=engine)

app = flask.Flask(__name__)

@app.teardown_appcontext
def shutdown_session(exception=None):
    db_session.remove()

@app.route('/')
def main():
    return flask.Response('Hello, world!', mimetype='text/plain')

@app.route('/get', methods=['POST'])
def get():
    id = flask.request.form['id']
    item = Item.query.get(id)
    return flask.Response('' if item is None else item.data, mimetype='application/octet-stream')

@app.route('/set', methods=['POST'])
def set():
    id = flask.request.form['id']
    old = flask.request.form['old']
    new = flask.request.form['new']
    item = Item.query.get(id)
    if item is None:
        item = Item(id=id, data='')
        db_session.add(item)
    if item.data != old:
        return flask.Response(item.data, mimetype='application/octet-stream', status='412 Precondition Failed')
    else:
        if new == '':
            db_session.delete(item)
        else:
            item.data = new
        db_session.commit()
        return flask.Response('', mimetype='text/plain')

@app.route('/poll', methods=['POST'])
def poll():
    id = flask.request.form['id']
    old = flask.request.form['old']
    while True:
        item = Item.query.get(id)
        if ('' if item is None else item.data) != old:
            break
        db_session.commit()
        time.sleep(1)
    return flask.Response('' if item is None else item.data, mimetype='application/octet-stream')

if __name__ == '__main__':
    flup.server.fcgi.WSGIServer(app).run()
